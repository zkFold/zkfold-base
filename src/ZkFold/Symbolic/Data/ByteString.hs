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
    ) where

import           Control.DeepSeq                                           (NFData)
import           Control.Monad                                             (replicateM)
import           Data.Bits                                                 as B
import qualified Data.ByteString                                           as Bytes
import           Data.Functor.Rep                                          (Representable (..))
import           Data.Kind                                                 (Type)
import           Data.List                                                 (foldl, reverse, unfoldr)
import           Data.Maybe                                                (Maybe (..))
import           Data.Proxy                                                (Proxy (..))
import           Data.String                                               (IsString (..))
import           Data.Traversable                                          (for)
import           GHC.Generics                                              (Generic, Par1 (..), U1 (..))
import           GHC.Natural                                               (naturalFromInteger)
import           GHC.TypeNats                                              (natVal)
import           Prelude                                                   (Integer, drop, fmap, otherwise, pure, take,
                                                                            type (~), ($), (.), (<$>), (<), (<>), (==),
                                                                            (>=))
import qualified Prelude                                                   as Haskell
import           Test.QuickCheck                                           (Arbitrary (..), chooseInteger)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                           (Zp, toZp)
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Data.Vector                                   as V
import           ZkFold.Base.Data.Vector                                   (Vector (..))
import           ZkFold.Prelude                                            (replicateA, (!!))
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators    (embedV)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal       (Var)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint
import           ZkFold.Symbolic.Data.Bool                                 (Bool (..), BoolType (..))
import           ZkFold.Symbolic.Data.Class                                (SymbolicData)
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Interpreter                               (Interpreter (..))
import           ZkFold.Symbolic.MonadCircuit                              (Arithmetic, newAssigned)

-- | A ByteString which stores @n@ bits and uses elements of @a@ as registers, one element per register.
-- Bit layout is Big-endian.
--
newtype ByteString (n :: Natural) (backend :: (Type -> Type) -> Type) = ByteString (backend (Vector n))
    deriving (Generic)

deriving stock instance Haskell.Show (b (Vector n)) => Haskell.Show (ByteString n b)
deriving stock instance Haskell.Eq (b (Vector n)) => Haskell.Eq (ByteString n b)
deriving anyclass instance NFData (b (Vector n)) => NFData (ByteString n b)
deriving newtype instance SymbolicData c (ByteString n c)

-- TODO
-- Since the only difference between ByteStrings on Zp and ByteStrings on ArithmeticCircuits is backend,
-- a lot of code below is actually repeating the same operations on different containers.
-- Perhaps we can reduce boilerplate code by introducing some generic operations on containers and reusing them.
--

instance
    ( FromConstant Natural (ByteString 8 b)
    , Concat (ByteString 8 b) (ByteString n b)
    ) => IsString (ByteString n b) where
    fromString = fromConstant . fromString @Bytes.ByteString

instance
    ( FromConstant Natural (ByteString 8 b)
    , Concat (ByteString 8 b) (ByteString n b)
    ) => FromConstant Bytes.ByteString (ByteString n b) where
    fromConstant bytes = concat $ fmap (fromConstant @Natural @(ByteString 8 b)
        . Haskell.fromIntegral
        . Haskell.toInteger) (Bytes.unpack bytes)

emptyByteString :: FromConstant Natural (ByteString 0 b) => ByteString 0 b
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


-- | Allows to check state of bits in a container @c@ of size @n@ with computational backend @b@
--
class BitState c n b where
    isSet :: c n b -> Natural -> Bool b
    isUnset :: c n b -> Natural -> Bool b


instance ToConstant (ByteString n (Interpreter (Zp p))) Natural where
    toConstant (ByteString (Interpreter bits)) = Haskell.foldl (\y p -> toConstant p + base * y) 0 bits
        where base = 2


instance (KnownNat n, Finite (Zp p)) => FromConstant Natural (ByteString n (Interpreter (Zp p))) where

    -- | Pack a ByteString using one field element per bit.
    -- @fromConstant@ discards bits after @n@.
    -- If the constant is greater than @2^n@, only the part modulo @2^n@ will be converted into a ByteString.
    --
    fromConstant n = ByteString . Interpreter . V.unsafeToVector $ toZp . Haskell.fromIntegral <$> toBsBits n (value @n)

instance (KnownNat n, Finite (Zp p)) => FromConstant Integer (ByteString n (Interpreter (Zp p))) where
    fromConstant = fromConstant . naturalFromInteger . (`Haskell.mod` (2 ^ getNatural @n))

instance (FromConstant Natural a, Arithmetic a, KnownNat n, Haskell.Ord (Rep i), Representable i) => FromConstant Natural (ByteString n (ArithmeticCircuit a i)) where

    -- | Pack a ByteString using one field element per bit.
    -- @fromConstant@ discards bits after @n@.
    -- If the constant is greater than @2^n@, only the part modulo @2^n@ will be converted into a ByteString.
    --
    fromConstant n = ByteString $ embedV $ V.unsafeToVector $ fromConstant <$> toBsBits n (value @n)

toBsBits :: Natural -> Natural -> [Natural]
toBsBits num n = reverse bits
    where
        base = 2

        availableBits = unfoldr (toBase base) (num `Haskell.mod` (2 Haskell.^ n)) <> Haskell.repeat 0

        bits = take (Haskell.fromIntegral n) availableBits

-- | Convert a number into @base@-ary system.
--
toBase :: Natural -> Natural -> Maybe (Natural, Natural)
toBase _ 0    = Nothing
toBase base b = let (d, m) = b `divMod` base in Just (m, d)


instance (FromConstant Natural a, Arithmetic a, KnownNat n, Haskell.Ord (Rep i), Representable i) => FromConstant Integer (ByteString n (ArithmeticCircuit a i)) where
    fromConstant = fromConstant . naturalFromInteger . (`Haskell.mod` (2 ^ getNatural @n))

instance (Finite (Zp p), KnownNat n) => Arbitrary (ByteString n (Interpreter (Zp p))) where
    arbitrary = ByteString . Interpreter . V.unsafeToVector <$> replicateA (value @n) (toss (1 :: Natural))
        where toss b = fromConstant <$> chooseInteger (0, 2 ^ b - 1)

instance (Finite (Zp p), KnownNat n) => ShiftBits (ByteString n (Interpreter (Zp p))) where

    shiftBits b s = fromConstant $ shift (toConstant @_ @Natural b) (Haskell.fromIntegral s) `Haskell.mod` (2 Haskell.^ (getNatural @n))

    -- | @Data.Bits.rotate@ works exactly as @Data.Bits.shift@ for @Natural@, we have to rotate bits manually.
    rotateBitsL b s
      | s == 0 = b
       -- Rotations by k * n + p bits where n is the length of the ByteString are equivalent to rotations by p bits.
      | s >= (getNatural @n) = rotateBitsL b (s `Haskell.mod` (getNatural @n))
      | otherwise = fromConstant $ d + m
        where
            nat :: Natural
            nat = toConstant b

            bound :: Natural
            bound = 2 Haskell.^ getNatural @n

            d, m :: Natural
            (d, m) = (nat `shiftL` Haskell.fromIntegral s) `Haskell.divMod` bound

    rotateBitsR b s
      | s == 0 = b
       -- Rotations by k * n + p bits where n is the length of the ByteString are equivalent to rotations by p bits.
      | s >= (getNatural @n) = rotateBitsR b (s `Haskell.mod` (getNatural @n))
      | otherwise = fromConstant $ d + m
        where
            nat :: Natural
            nat = toConstant b

            intS :: Haskell.Int
            intS = Haskell.fromIntegral s

            m :: Natural
            m = (nat `Haskell.mod` (2 Haskell.^ intS)) `shiftL` (Haskell.fromIntegral (getNatural @n) Haskell.- intS)

            d :: Natural
            d = nat `shiftR` intS

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
    ( KnownNat wordSize
    , (Div n wordSize) * wordSize ~ n
    , (Div wordSize 8) * 8 ~ wordSize
    ) => ReverseEndianness wordSize (ByteString n (Interpreter (Zp p))) where
    reverseEndianness (ByteString (Interpreter v)) = ByteString . Interpreter $ reverseEndianness' @wordSize v

instance (Finite (Zp p), KnownNat n) => BoolType (ByteString n (Interpreter (Zp p))) where
    false = fromConstant (0 :: Natural)

    -- | A ByteString with all bits set to 1 is the unity for bitwise and.
    true = not false

    -- | bitwise not.
    -- @Data.Bits.complement@ is undefined for @Natural@, we have to flip bits manually.
    not = fromConstant @Natural . (nextPow2 -!) . toConstant
      where
        nextPow2 :: Natural
        nextPow2 = (2 ^ natVal (Proxy @n)) -! 1

    -- | Bitwise or
    x || y = fromConstant @Natural $ toConstant x .|. toConstant y

    -- | Bitwise and
    x && y = fromConstant @Natural $ toConstant x .&. toConstant y

    -- | Bitwise xor
    xor x y = fromConstant @Natural $ toConstant x `B.xor` toConstant y


-- | A ByteString of length @n@ can only be split into words of length @wordSize@ if all of the following conditions are met:
-- 1. @wordSize@ is not greater than @n@;
-- 2. @wordSize@ is not zero;
-- 3. The bytestring is not empty;
-- 4. @wordSize@ divides @n@.
--
instance
  ( KnownNat wordSize
  , KnownNat n
  , Finite (Zp p)
  , wordSize <= n
  , 1 <= wordSize
  , 1 <= n
  , Mod n wordSize ~ 0
  ) => ToWords (ByteString n (Interpreter (Zp p))) (ByteString wordSize (Interpreter (Zp p))) where

    toWords bs = fmap fromConstant $ reverse $ take (Haskell.fromIntegral $ n `Haskell.div` wordSize) natWords
      where
        asNat :: Natural
        asNat = toConstant bs

        n :: Natural
        n = getNatural @n

        wordSize :: Natural
        wordSize = getNatural @wordSize

        natWords :: [Natural]
        natWords = unfoldr (toBase (2 Haskell.^ wordSize)) asNat <> Haskell.repeat (fromConstant @Natural 0)

-- | Unfortunately, Haskell does not support dependent types yet,
-- so we have no possibility to infer the exact type of the result
-- (the list can contain an arbitrary number of words).
-- We can only impose some restrictions on @n@ and @m@.
--
instance
  ( KnownNat m
  , KnownNat k
  , Mod k m ~ 0
  , Finite (Zp p)
  ) => Concat (ByteString m (Interpreter (Zp p))) (ByteString k (Interpreter (Zp p))) where

    concat = fromConstant @Natural . foldl (\p y -> toConstant y + p `shift` m) 0
        where
            m = Haskell.fromIntegral $ value @m


-- | Only a bigger ByteString can be truncated into a smaller one.
--
instance
  ( KnownNat m
  , KnownNat n
  , n <= m
  , Finite (Zp p)
  ) => Truncate (ByteString m (Interpreter (Zp p))) (ByteString n (Interpreter (Zp p))) where

    truncate = fromConstant @Natural . (`shiftR` diff) . toConstant
        where
            diff :: Haskell.Int
            diff = Haskell.fromIntegral $ getNatural @m Haskell.- getNatural @n

-- | Only a smaller ByteString can be extended into a bigger one.
--
instance
  ( KnownNat n
  , m <= n
  , Finite (Zp p)
  ) => Extend (ByteString m (Interpreter (Zp p))) (ByteString n (Interpreter (Zp p))) where

    extend = fromConstant @Natural . toConstant

instance Finite (Zp p) => BitState ByteString n (Interpreter (Zp p)) where
    isSet (ByteString (Interpreter v)) ix = Bool (Interpreter . Par1 . (!! ix) . V.fromVector $ v)
    isUnset bs ix = let Bool (Interpreter zp) = isSet bs ix
                     in Bool (Interpreter $ (one -) <$> zp)

--------------------------------------------------------------------------------

instance (Arithmetic a, KnownNat n, Haskell.Ord (Rep i), Representable i) => ShiftBits (ByteString n (ArithmeticCircuit a i)) where
    shiftBits bs@(ByteString oldBits) s
      | s == 0 = bs
      | Haskell.abs s >= Haskell.fromIntegral (getNatural @n) = false
      | otherwise = ByteString $ circuitF solve
      where
        solve :: forall v m. MonadBlueprint i v a m => m (Vector n v)
        solve = do
            bits  <- V.fromVector <$> runCircuit oldBits
            zeros <- replicateM (Haskell.fromIntegral $ Haskell.abs s) $ newAssigned (Haskell.const zero)

            let newBits = case s < 0 of
                        Haskell.True  -> take (Haskell.fromIntegral $ getNatural @n) $ zeros <> bits
                        Haskell.False -> drop (Haskell.fromIntegral s) $ bits <> zeros

            pure $ V.unsafeToVector newBits


    -- | rotateBits does not even require operations on the circuit.
    --
    rotateBits (ByteString bits) s = ByteString (bits { acOutput = V.rotate (acOutput bits) s})

instance
    ( KnownNat wordSize
    , (Div n wordSize) * wordSize ~ n
    , (Div wordSize 8) * 8 ~ wordSize
    ) => ReverseEndianness wordSize (ByteString n (ArithmeticCircuit a i)) where
        reverseEndianness (ByteString v) = ByteString $ v { acOutput = reverseEndianness' @wordSize (acOutput v) }


-- | A generic bitwise operation on two ByteStrings.
-- TODO: Shall we expose it to users? Can they do something malicious having such function? AFAIK there are checks that constrain each bit to 0 or 1.
--
bitwiseOperation
    :: forall a i n
    .  (Arithmetic a, Haskell.Ord (Rep i), Representable i)
    => ByteString n (ArithmeticCircuit a i)
    -> ByteString n (ArithmeticCircuit a i)
    -> (forall v. v -> v -> ClosedPoly v a)
    -> ByteString n (ArithmeticCircuit a i)
bitwiseOperation (ByteString bits1) (ByteString bits2) cons = ByteString $ circuitF solve
  where
    solve :: forall v m. MonadBlueprint i v a m => m (Vector n v)
    solve = do
        varsLeft  <- runCircuit bits1
        varsRight <- runCircuit bits2
        V.zipWithM applyBitwise varsLeft varsRight

    applyBitwise :: forall v m . MonadBlueprint i v a m => v -> v -> m v
    applyBitwise l r = newAssigned $ cons l r


instance (Arithmetic a, KnownNat n, Haskell.Ord (Rep i), Representable i) => BoolType (ByteString n (ArithmeticCircuit a i)) where
    false = ByteString $ embedV (pure zero)

    true = not false

    not (ByteString bits) = ByteString (flipBits bits)
        where
            flipBits r = circuitF $ do
                is <- runCircuit r
                for is $ \i -> newAssigned (\p -> one - p i)

    l || r = bitwiseOperation l r (\i j x -> let xi = x i
                                                 xj = x j
                                              in xi + xj - xi * xj)

    l && r = bitwiseOperation l r (\i j x -> x i * x j)

    xor l r = bitwiseOperation l r (\i j x -> let xi = x i
                                                  xj = x j
                                               in xi + xj - (xi * xj + xi * xj))


instance
  ( KnownNat wordSize
  , Mod n wordSize ~ 0
  , (Div n wordSize) * wordSize ~ n
  ) => ToWords (ByteString n (ArithmeticCircuit a i)) (ByteString wordSize (ArithmeticCircuit a i)) where

    toWords (ByteString bits) = (\o -> ByteString $ bits { acOutput = o} ) <$> V.fromVector (V.chunks @(Div n wordSize) @wordSize $ acOutput bits)


instance
  ( Mod k m ~ 0
  , (Div k m) * m ~ k
  , Arithmetic a
  ) => Concat (ByteString m (ArithmeticCircuit a i)) (ByteString k (ArithmeticCircuit a i)) where

    concat bs = ByteString $ bsCircuit {acOutput = bsOutputs}
        where
            bsCircuit = Haskell.mconcat $ (\(ByteString bits) -> bits {acOutput = U1}) <$> bs

            bsOutputs :: Vector k (Var i)
            bsOutputs = V.unsafeConcat @(Div k m) $ (\(ByteString bits) -> acOutput bits) <$> bs

instance
  ( KnownNat n
  , n <= m
  ) => Truncate (ByteString m (ArithmeticCircuit a i)) (ByteString n (ArithmeticCircuit a i)) where

    truncate (ByteString bits) = ByteString $ bits { acOutput = V.take @n (acOutput bits) }

instance
  ( KnownNat m
  , KnownNat n
  , m <= n
  , Arithmetic a, Haskell.Ord (Rep i), Representable i
  ) => Extend (ByteString m (ArithmeticCircuit a i)) (ByteString n (ArithmeticCircuit a i)) where

    extend (ByteString oldBits) = ByteString $ circuitF (Vector <$> solve)
      where
        solve :: forall v m'. MonadBlueprint i v a m' => m' [v]
        solve = do
            bits <- runCircuit oldBits
            zeros <- replicateM diff $ newAssigned (Haskell.const zero)
            pure $ zeros <> V.fromVector bits

        diff :: Haskell.Int
        diff = Haskell.fromIntegral $ getNatural @n Haskell.- getNatural @m


instance (Arithmetic a, Haskell.Ord (Rep i), Representable i) => BitState ByteString n (ArithmeticCircuit a i) where
    isSet (ByteString v) ix = Bool $ circuit solve
        where
            solve :: forall v m . MonadBlueprint i v a m => m v
            solve = (!! ix) . V.fromVector <$> runCircuit v
    isUnset (ByteString v) ix = Bool $ circuit solve
        where
            solve :: forall v m . MonadBlueprint i v a m => m v
            solve = do
                i <- (!! ix) . V.fromVector <$> runCircuit v
                newAssigned $ \p -> one - p i
