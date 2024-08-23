{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module ZkFold.Symbolic.Data.ByteString
    ( ByteString(..)
    , ShiftBits (..)
    , ReverseEndianness (..)
    , BitState (..)
    , ToWords (..)
    , Concat (..)
    , Truncate (..)
    , emptyByteString
    , toBsBits
    ) where

import           Control.DeepSeq                  (NFData)
import           Control.Monad                    (replicateM)
import qualified Data.ByteString                  as Bytes
import           Data.Kind                        (Type)
import           Data.List                        (reverse, unfoldr)
import           Data.Maybe                       (Maybe (..))
import           Data.String                      (IsString (..))
import           Data.Traversable                 (for)
import           GHC.Generics                     (Generic, Par1 (..))
import           GHC.Natural                      (naturalFromInteger)
import           Prelude                          (Integer, drop, fmap, otherwise, pure, return, take, type (~), ($),
                                                   (.), (<$>), (<), (<>), (==), (>=))
import qualified Prelude                          as Haskell
import           Test.QuickCheck                  (Arbitrary (..), chooseInteger)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field  (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.HFunctor        (HFunctor (..))
import           ZkFold.Base.Data.Package         (packed, unpacked)
import qualified ZkFold.Base.Data.Vector          as V
import           ZkFold.Base.Data.Vector          (Vector (..))
import           ZkFold.Prelude                   (replicateA, (!!))
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool        (Bool (..), BoolType (..))
import           ZkFold.Symbolic.Data.Class       (SymbolicData)
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Interpreter      (Interpreter (..))
import           ZkFold.Symbolic.MonadCircuit     (ClosedPoly, MonadCircuit, newAssigned)


-- | A ByteString which stores @n@ bits and uses elements of @a@ as registers, one element per register.
-- Bit layout is Big-endian.
--
newtype ByteString (n :: Natural) (context :: (Type -> Type) -> Type) = ByteString (context (Vector n))
    deriving (Generic)

deriving stock instance Haskell.Show (c (Vector n)) => Haskell.Show (ByteString n c)
deriving stock instance Haskell.Eq (c (Vector n)) => Haskell.Eq (ByteString n c)
deriving anyclass instance NFData (c (Vector n)) => NFData (ByteString n c)
deriving newtype instance SymbolicData (ByteString n c)

instance
    ( FromConstant Natural (ByteString 8 c)
    , Concat (ByteString 8 c) (ByteString n c)
    ) => IsString (ByteString n c) where
    fromString = fromConstant . fromString @Bytes.ByteString

instance
    ( FromConstant Natural (ByteString 8 c)
    , Concat (ByteString 8 c) (ByteString n c)
    ) => FromConstant Bytes.ByteString (ByteString n c) where
    fromConstant bytes = concat $ fmap (fromConstant @Natural @(ByteString 8 c)
        . Haskell.fromIntegral
        . Haskell.toInteger) (Bytes.unpack bytes)

emptyByteString :: FromConstant Natural (ByteString 0 c) => ByteString 0 c
emptyByteString = fromConstant @Natural 0


-- | A class for data types that support bit shift and bit cyclic shift (rotation) operations.
--
class ShiftBits a where
    {-# MINIMAL (shiftBits | (shiftBitsL, shiftBitsR)), (rotateBits | (rotateBitsL, rotateBitsR)) #-}

    -- | shiftBits performs a left shift when its agrument is greater than zero and a right shift otherwise.
    --
    shiftBits :: a -> Integer -> a
    shiftBits a s
      | s < 0     = shiftBitsR a (Haskell.fromIntegral . negate $ s)
      | otherwise = shiftBitsL a (Haskell.fromIntegral s)

    shiftBitsL :: a -> Natural -> a
    shiftBitsL a s = shiftBits a (Haskell.fromIntegral s)

    shiftBitsR :: a -> Natural -> a
    shiftBitsR a s = shiftBits a (negate . Haskell.fromIntegral $ s)

    -- | rotateBits performs a left cyclic shift when its agrument is greater than zero and a right cyclic shift otherwise.
    --
    rotateBits :: a -> Integer -> a
    rotateBits a s
      | s < 0     = rotateBitsR a (Haskell.fromIntegral . negate $ s)
      | otherwise = rotateBitsL a (Haskell.fromIntegral s)

    rotateBitsL :: a -> Natural -> a
    rotateBitsL a s = rotateBits a (Haskell.fromIntegral s)

    rotateBitsR :: a -> Natural -> a
    rotateBitsR a s = rotateBits a (negate . Haskell.fromIntegral $ s)

class ReverseEndianness wordSize a where
    reverseEndianness :: a -> a

-- | Describes types which can be split into words of equal size.
-- Parameters have to be of different types as ByteString store their lengths on type level and hence after splitting they chagne types.
--
class ToWords a b where
    toWords :: a -> [b]


-- | Describes types which can be made by concatenating several words of equal length.
--
class Concat a b where
    concat :: [a] -> b


-- | Describes types that can be truncated by dropping several bits from the end (i.e. stored in the lower registers)
--
class Truncate a b where
    truncate :: a -> b


-- | Allows to check state of bits in a container @c@ of size @n@ with computational context @b@
--
class BitState c n b where
    isSet :: c n b -> Natural -> Bool b
    isUnset :: c n b -> Natural -> Bool b


instance ToConstant (ByteString n (Interpreter (Zp p))) Natural where
    toConstant (ByteString (Interpreter bits)) = Haskell.foldl (\y p -> toConstant p + base * y) 0 bits
        where base = 2


    -- | Pack a ByteString using one field element per bit.
    -- @fromConstant@ discards bits after @n@.
    -- If the constant is greater than @2^n@, only the part modulo @2^n@ will be converted into a ByteString.
instance (Symbolic c, KnownNat n) => FromConstant Natural (ByteString n c) where
    fromConstant n = ByteString . embed @c $ V.unsafeToVector $ fromConstant <$> toBsBits n (value @n)

instance (Symbolic c, KnownNat n) => FromConstant Integer (ByteString n c) where
    fromConstant = fromConstant . naturalFromInteger . (`Haskell.mod` (2 ^ getNatural @n))

instance (Symbolic c, KnownNat n) => Arbitrary (ByteString n c) where
    arbitrary = ByteString . embed @c . V.unsafeToVector <$> replicateA (value @n) (toss (1 :: Natural))
        where toss b = fromConstant <$> chooseInteger (0, 2 ^ b - 1)

reverseEndianness' :: forall wordSize n x .
    ( KnownNat wordSize
    , (Div n wordSize) * wordSize ~ n
    , (Div wordSize 8) * 8 ~ wordSize
    ) => Vector n x -> Vector n x
reverseEndianness' v =
    let chunks = V.chunks @(Div n wordSize) @wordSize v
        chunks' = fmap (V.concat . V.reverse . V.chunks @(Div wordSize 8) @8) chunks
     in V.concat chunks'

instance
    ( Symbolic c
    , KnownNat wordSize
    , (Div n wordSize) * wordSize ~ n
    , (Div wordSize 8) * 8 ~ wordSize
    ) => ReverseEndianness wordSize (ByteString n c) where
    reverseEndianness (ByteString v) = ByteString $ hmap (reverseEndianness' @wordSize) v

instance (Symbolic c, KnownNat n) => BoolType (ByteString n c) where
    false = fromConstant (0 :: Natural)
    true = not false

    not (ByteString bits) =  ByteString $ fromCircuitF bits solve
        where
            solve :: MonadCircuit i (BaseField c) m => Vector n i -> m (Vector n i)
            solve xv = do
                let xs = V.fromVector xv
                ys <-  for xs $ \i -> newAssigned (\p -> one - p i)
                return $ V.unsafeToVector ys

    l || r =  bitwiseOperation l r cons
        where
            cons i j x =
                        let xi = x i
                            xj = x j
                        in xi + xj - xi * xj

    l && r = bitwiseOperation l r cons
        where
            cons i j x =
                        let xi = x i
                            xj = x j
                        in xi * xj

    xor l r = bitwiseOperation l r cons
        where
            cons i j x =
                        let xi = x i
                            xj = x j
                        in xi + xj - (xi * xj + xi * xj)

-- | A ByteString of length @n@ can only be split into words of length @wordSize@ if all of the following conditions are met:
-- 1. @wordSize@ is not greater than @n@;
-- 2. @wordSize@ is not zero;
-- 3. The bytestring is not empty;
-- 4. @wordSize@ divides @n@.
--

instance
  ( Symbolic c
  , KnownNat wordSize
  , (Div n wordSize) * wordSize ~ n
  ) => ToWords (ByteString n c) (ByteString wordSize c) where
    toWords (ByteString bits) = Haskell.map (ByteString . packed) $ V.fromVector . V.chunks @(Div n wordSize) @wordSize $ unpacked bits

-- | Unfortunately, Haskell does not support dependent types yet,
-- so we have no possibility to infer the exact type of the result
-- (the list can contain an arbitrary number of words).
-- We can only impose some restrictions on @n@ and @m@.
--

instance
  ( Symbolic c
  , Mod k m ~ 0
  , (Div k m) * m ~ k
  ) => Concat (ByteString m c) (ByteString k c) where
    concat bs = (ByteString . packed) $ V.unsafeConcat @(Div k m) ( Haskell.map (\(ByteString bits) -> unpacked bits) bs)

instance
  ( Symbolic c
  , KnownNat n
  , n <= m
  ) => Truncate (ByteString m c) (ByteString n c) where
    truncate (ByteString bits) = ByteString $ hmap (V.take @n) bits

--------------------------------------------------------------------------------
instance (Symbolic c, KnownNat n) => ShiftBits (ByteString n c) where
    shiftBits bs@(ByteString oldBits) s
      | s == 0 = bs
      | Haskell.abs s >= Haskell.fromIntegral (getNatural @n) = false
      | otherwise = ByteString $ symbolicF oldBits (\v ->  V.shift v s (fromConstant (0 :: Integer))) solve
      where
        solve :: forall i m. MonadCircuit i (BaseField c) m => Vector n i -> m (Vector n i)
        solve bitsV = do
            let bits = V.fromVector bitsV
            zeros <- replicateM (Haskell.fromIntegral $ Haskell.abs s) $ newAssigned (Haskell.const zero)

            let newBits = case s < 0 of
                        Haskell.True  -> take (Haskell.fromIntegral $ getNatural @n) $ zeros <> bits
                        Haskell.False -> drop (Haskell.fromIntegral s) $ bits <> zeros

            pure $ V.unsafeToVector newBits

    rotateBits (ByteString bits) s = ByteString $ hmap (`V.rotate` s) bits

instance
  ( Symbolic c
  , KnownNat k
  , KnownNat n
  , k <= n
  ) => Extend (ByteString k c) (ByteString n c) where
    extend (ByteString oldBits) = ByteString $ symbolicF oldBits (\v ->  V.unsafeToVector $ zeroA <> V.fromVector v) solve
      where
        solve :: forall i m. MonadCircuit i (BaseField c) m => Vector k i -> m (Vector n i)
        solve bitsV = do
            let bits = V.fromVector bitsV
            zeros <- replicateM diff $ newAssigned (Haskell.const zero)
            return $ V.unsafeToVector $ zeros <> bits

        diff :: Haskell.Int
        diff = Haskell.fromIntegral $ getNatural @n Haskell.- getNatural @k

        zeroA = Haskell.replicate diff (fromConstant (0 :: Integer ))

instance Symbolic c => BitState ByteString n c where
    isSet (ByteString bits) ix = Bool $ fromCircuitF bits solve
        where
            solve :: forall i m . MonadCircuit i (BaseField c) m => Vector n i -> m (Par1 i)
            solve v = do
                let vs = V.fromVector v
                return $ Par1 $ (!! ix) vs

    isUnset (ByteString bits) ix = Bool $ fromCircuitF bits solve
        where
            solve :: forall i m . MonadCircuit i (BaseField c) m => Vector n i -> m (Par1 i)
            solve v = do
                let vs = V.fromVector v
                    i = (!! ix) vs
                j <- newAssigned $ \p -> one - p i
                return $ Par1 j

--------------------------------------------------------------------------------

toBsBits :: Natural -> Natural -> [Natural]
toBsBits num n = reverse bits
    where
        base = 2

        availableBits = unfoldr (toBase base) (num `Haskell.mod` (2 Haskell.^ n)) <> Haskell.repeat 0

        bits = take (Haskell.fromIntegral n) availableBits

-- | Convert a number into @base@-ary system.

toBase :: Natural -> Natural -> Maybe (Natural, Natural)
toBase _ 0    = Nothing
toBase base b = let (d, m) = b `divMod` base in Just (m, d)


-- | A generic bitwise operation on two ByteStrings.
-- TODO: Shall we expose it to users? Can they do something malicious having such function? AFAIK there are checks that constrain each bit to 0 or 1.
--
bitwiseOperation
    :: forall c n
    .  Symbolic c
    => ByteString n c
    -> ByteString n c
    -> (forall i. i -> i -> ClosedPoly i (BaseField c))
    -> ByteString n c
bitwiseOperation (ByteString bits1) (ByteString bits2) cons = ByteString $ fromCircuit2F bits1 bits2 solve
    where
        solve :: MonadCircuit i (BaseField c) m => Vector n i -> Vector n i -> m (Vector n i)
        solve lv rv = do
            let varsLeft = lv
                varsRight = rv
            V.zipWithM  (\i j -> newAssigned $ cons i j) varsLeft varsRight
