{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module ZkFold.Symbolic.Data.ByteString
    ( ByteString(..)
    , ShiftBits (..)
    , reverseEndianness
    , isSet
    , isUnset
    , toWords
    , concat
    , Truncate (..)
    , emptyByteString
    , toBsBits
    ) where

import           Control.DeepSeq                    (NFData)
import           Control.Monad                      (replicateM)
import qualified Data.Bits                          as B
import qualified Data.ByteString                    as Bytes
import           Data.Kind                          (Type)
import           Data.List                          (reverse, unfoldr)
import           Data.Maybe                         (Maybe (..))
import           Data.String                        (IsString (..))
import           Data.Traversable                   (for)
import           GHC.Generics                       (Generic, Par1 (..))
import           GHC.Natural                        (naturalFromInteger)
import           Prelude                            (Integer, drop, fmap, otherwise, pure, return, take, type (~), ($),
                                                     (.), (<$>), (<), (<>), (==), (>=))
import qualified Prelude                            as Haskell
import           Test.QuickCheck                    (Arbitrary (..), chooseInteger)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field    (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.HFunctor          (HFunctor (..))
import           ZkFold.Base.Data.Package           (packed, unpacked)
import qualified ZkFold.Base.Data.Vector            as V
import           ZkFold.Base.Data.Vector            (Vector (..), parFmap)
import           ZkFold.Prelude                     (replicateA, (!!))
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool          (Bool (..), BoolType (..))
import           ZkFold.Symbolic.Data.Class         (SymbolicData)
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Eq            (Eq)
import           ZkFold.Symbolic.Data.Eq.Structural
import           ZkFold.Symbolic.Data.FieldElement  (FieldElement)
import           ZkFold.Symbolic.Interpreter        (Interpreter (..))
import           ZkFold.Symbolic.MonadCircuit       (ClosedPoly, MonadCircuit, newAssigned)

-- | A ByteString which stores @n@ bits and uses elements of @a@ as registers, one element per register.
-- Bit layout is Big-endian.
--
newtype ByteString (n :: Natural) (context :: (Type -> Type) -> Type) = ByteString (context (Vector n))
    deriving (Generic)

deriving stock instance Haskell.Show (c (Vector n)) => Haskell.Show (ByteString n c)
deriving stock instance Haskell.Eq (c (Vector n)) => Haskell.Eq (ByteString n c)
deriving anyclass instance NFData (c (Vector n)) => NFData (ByteString n c)
deriving newtype instance SymbolicData (ByteString n c)


deriving via (Structural (ByteString n c))
         instance (Symbolic c) => Eq (Bool c) (ByteString n c)

instance
    ( Symbolic c
    , FromConstant Natural (ByteString 8 c)
    , m * 8 ~ n
    ) => IsString (ByteString n c) where
    fromString = fromConstant . fromString @Bytes.ByteString

instance
    ( Symbolic c
    , FromConstant Natural (ByteString 8 c)
    , m * 8 ~ n
    ) => FromConstant Bytes.ByteString (ByteString n c) where
    fromConstant bytes = concat @8 @_ @n $ V.parFmap (fromConstant @Natural @(ByteString 8 c)
        . Haskell.fromIntegral
        . Haskell.toInteger) (V.unsafeToVector @m $ Bytes.unpack bytes)

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

-- | Describes types that can be truncated by dropping several bits from the end (i.e. stored in the lower registers)
--
class Truncate a b where
    truncate :: a -> b

instance ToConstant (ByteString n (Interpreter (Zp p))) where
    type Const (ByteString n (Interpreter (Zp p))) = Natural
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

reverseEndianness' :: forall wordSize k m n x.
    ( KnownNat wordSize
    , k * wordSize ~ n
    , m * 8 ~ wordSize
    ) => Vector n x -> Vector n x
reverseEndianness' v =
    let chunks = V.chunks @k @wordSize v
        chunks' = fmap (V.concat . V.reverse . V.chunks @m @8) chunks
     in V.concat chunks'

reverseEndianness :: forall wordSize k c n m. 
    ( Symbolic c
    , KnownNat wordSize
    , k * wordSize ~ n
    , m * 8 ~ wordSize
    ) => ByteString n c -> ByteString n c
reverseEndianness (ByteString v) = ByteString $ hmap (reverseEndianness' @wordSize @k) v

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

    xor (ByteString l) (ByteString r) = ByteString $ symbolic2F l r (\x y -> V.unsafeToVector $ fromConstant <$> toBsBits (vecToNat x `B.xor` vecToNat y) (value @n)) solve
        where
            vecToNat :: (ToConstant a, Const a ~ Natural) => Vector n a -> Natural
            vecToNat =  Haskell.foldl (\x p -> toConstant p + 2 * x :: Natural) 0

            solve :: MonadCircuit i (BaseField c) m => Vector n i -> Vector n i -> m (Vector n i)
            solve lv rv = do
                let varsLeft = lv
                    varsRight = rv
                V.zipWithM  (\i j -> newAssigned $ cons i j) varsLeft varsRight

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

toWords :: forall k wordSize n c. (Symbolic c, KnownNat wordSize, k * wordSize ~ n) => ByteString n c -> Vector k (ByteString wordSize c)
toWords (ByteString bits) = parFmap (ByteString . packed) $ V.chunks @k @wordSize $ unpacked bits

-- | Unfortunately, Haskell does not support dependent types yet,
-- so we have no possibility to infer the exact type of the result
-- (the list can contain an arbitrary number of words).
-- We can only impose some restrictions on @n@ and @m@.
--
concat :: forall m k n c. (Symbolic c, k * m ~ n) => Vector k (ByteString m c) -> ByteString n c
concat bs = (ByteString . packed) $ V.concat ( V.parFmap (\(ByteString bits) -> unpacked bits) bs)

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
        solve :: forall a m. MonadCircuit a (BaseField c) m => Vector n a -> m (Vector n a)
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

isSet :: forall c n. Symbolic c => ByteString n c -> Natural -> Bool c
isSet (ByteString bits) ix = Bool $ fromCircuitF bits solve
    where
        solve :: forall i m . MonadCircuit i (BaseField c) m => Vector n i -> m (Par1 i)
        solve v = do
            let vs = V.fromVector v
            return $ Par1 $ (!! ix) vs

isUnset :: forall c n. Symbolic c => ByteString n c -> Natural -> Bool c
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

instance (Symbolic c, NumberOfBits (BaseField c) ~ n) => Iso (FieldElement c) (ByteString n c) where
  from = ByteString . binaryExpansion

instance (Symbolic c, NumberOfBits (BaseField c) ~ n) => Iso (ByteString n c) (FieldElement c) where
  from (ByteString a) = fromBinary a
