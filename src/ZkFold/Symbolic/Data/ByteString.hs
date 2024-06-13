{-# LANGUAGE AllowAmbiguousTypes          #-}
{-# LANGUAGE DeriveAnyClass               #-}
{-# LANGUAGE DerivingStrategies           #-}
{-# LANGUAGE NoGeneralisedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications             #-}
{-# LANGUAGE TypeOperators                #-}
{-# LANGUAGE UndecidableInstances         #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- Trust me bro

module ZkFold.Symbolic.Data.ByteString
    ( ByteString(..)
    , ShiftBits (..)
    , ToWords (..)
    , Concat (..)
    , Truncate (..)
    ) where

import           Control.DeepSeq                                           (NFData)
import           Control.Monad                                             (replicateM)
import           Data.Bits                                                 as B
import qualified Data.ByteString                                           as Bytes
import           Data.Kind                                                 (Type)
import           Data.List                                                 (foldl, reverse, unfoldr)
import           Data.Maybe                                                (Maybe (..))
import           Data.Proxy                                                (Proxy (..))
import           Data.String                                               (IsString (..))
import           Data.Traversable                                          (for)
import           GHC.Generics                                              (Generic)
import           GHC.Natural                                               (naturalFromInteger)
import           GHC.TypeNats                                              (Div, Mod, Natural, natVal)
import           Prelude                                                   (Bool (..), Integer, drop, fmap, otherwise,
                                                                            pure, take, type (~), ($), (.), (<$>), (<),
                                                                            (<>), (==), (>=))
import qualified Prelude                                                   as Haskell
import           Test.QuickCheck                                           (Arbitrary (..), chooseInteger)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                           (Zp, toZp)
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Data.Vector                                   as V
import           ZkFold.Base.Data.Vector                                   (Vector (..))
import           ZkFold.Prelude                                            (replicateA)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators    (embedV)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal       (acCircuit)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint
import           ZkFold.Symbolic.Data.Bool                                 (BoolType (..))
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.UInt


-- | A ByteString which stores @n@ bits and uses elements of @a@ as registers, one element per register.
-- Bit layout is Big-endian.
--
-- data family ByteString (n :: Natural) (a :: Type)

newtype ByteString (n :: Natural) (backend :: Natural -> Type -> Type) (a :: Type) = ByteString (backend n a)
    deriving (Haskell.Show, Haskell.Eq, Generic, NFData)

instance
    ( FromConstant Natural a
    , Concat (ByteString 8 a) (ByteString n a)
    ) => IsString (ByteString n a) where
    fromString = fromConstant . fromString @Bytes.ByteString

instance
    ( FromConstant Natural a
    , Concat (ByteString 8 a) (ByteString n a)
    ) => FromConstant Bytes.ByteString (ByteString n a) where
    fromConstant bytes = concat
        $ fromConstant @Natural @(ByteString 8 a)
        . Haskell.fromIntegral
        . Haskell.toInteger
        <$> Bytes.unpack bytes

{--
data instance ByteString n (Zp p) = ByteString [Zp p]
    deriving (Haskell.Show, Haskell.Eq, Generic, NFData)

data instance ByteString n (ArithmeticCircuit n a) = ByteString (ArithmeticCircuit n a)
    deriving (Haskell.Show, Generic, NFData)
--}

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


instance ToConstant (ByteString n Vector (Zp p)) Natural where
    toConstant (ByteString bits) = Haskell.foldl (\y p -> toConstant p + base * y) 0 bits
        where base = 2


instance (KnownNat n, Finite (Zp p)) => FromConstant Natural (ByteString n Vector (Zp p)) where

    -- | Pack a ByteString using one field element per bit.
    -- @fromConstant@ discards bits after @n@.
    -- If the constant is greater than @2^n@, only the part modulo @2^n@ will be converted into a ByteString.
    --
    fromConstant n = ByteString . V.unsafeToVector $ toZp . Haskell.fromIntegral <$> toBsBits n (value @n)

instance (KnownNat n, Finite (Zp p)) => FromConstant Integer (ByteString n Vector (Zp p)) where
    fromConstant = fromConstant . naturalFromInteger . (`Haskell.mod` (2 ^ getNatural @n))

instance (FromConstant Natural a, Arithmetic a, KnownNat n) => FromConstant Natural (ByteString n ArithmeticCircuit a) where

    -- | Pack a ByteString using one field element per bit.
    -- @fromConstant@ discards bits after @n@.
    -- If the constant is greater than @2^n@, only the part modulo @2^n@ will be converted into a ByteString.
    --
    fromConstant n = ByteString $ embedV $ V.unsafeToVector $ fmap fromConstant $ toBsBits n (value @n)

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


instance (FromConstant Natural a, Arithmetic a, KnownNat n) => FromConstant Integer (ByteString n ArithmeticCircuit a) where
    fromConstant = fromConstant . naturalFromInteger . (`Haskell.mod` (2 ^ getNatural @n))

instance (Finite (Zp p), KnownNat n) => Iso (ByteString n Vector (Zp p)) (UInt n Vector (Zp p)) where
    from bs = fromConstant @Natural . toConstant $ bs

instance (Finite (Zp p), KnownNat n) => Iso (UInt n Vector (Zp p)) (ByteString n Vector (Zp p)) where
    from ui = fromConstant @Natural . toConstant $ ui

instance (Finite (Zp p), KnownNat n) => Arbitrary (ByteString n Vector (Zp p)) where
    arbitrary = ByteString . V.unsafeToVector <$> replicateA (value @n) (toss (1 :: Natural))
        where toss b = fromConstant <$> chooseInteger (0, 2 ^ b - 1)

instance (Finite (Zp p), KnownNat n) => ShiftBits (ByteString n Vector (Zp p)) where

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


instance (Finite (Zp p), KnownNat n) => BoolType (ByteString n Vector (Zp p)) where
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
  ) => ToWords (ByteString n Vector (Zp p)) (ByteString wordSize Vector (Zp p)) where

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
  ( KnownNat n
  , KnownNat m
  , m <= n
  , Mod n m ~ 0
  , Finite (Zp p)
  ) => Concat (ByteString m Vector (Zp p)) (ByteString n Vector (Zp p)) where

    concat = fromConstant @Natural . foldl (\p y -> toConstant y + p `shift` m) 0
        where
            m = Haskell.fromIntegral $ getNatural @m


-- | Only a bigger ByteString can be truncated into a smaller one.
--
instance
  ( KnownNat m
  , KnownNat n
  , n <= m
  , Finite (Zp p)
  ) => Truncate (ByteString m Vector (Zp p)) (ByteString n Vector (Zp p)) where

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
  ) => Extend (ByteString m Vector (Zp p)) (ByteString n Vector (Zp p)) where

    extend = fromConstant @Natural . toConstant

--------------------------------------------------------------------------------

instance (Arithmetic a, KnownNat n) => SymbolicData a n (ByteString n ArithmeticCircuit a) where
    pieces (ByteString bits) = bits

    restore c o = ByteString $ c `withOutputs` o


instance (Arithmetic a, KnownNat n) => Iso (ByteString n ArithmeticCircuit a) (UInt n ArithmeticCircuit a) where
    from (ByteString bits) = UInt (circuitN $ V.unsafeToVector <$> solve)
        where
            solve :: forall i m. MonadBlueprint i a m => m [i]
            solve = do
                bsBits <- V.fromVector <$> runCircuit bits
                fromBits (highRegisterSize @a @n) (registerSize @a @n) bsBits

instance (Arithmetic a, KnownNat n) => Iso (UInt n ArithmeticCircuit a) (ByteString n ArithmeticCircuit a) where
    from (UInt ac) = ByteString $ circuitN $ Vector <$> solve
        where
            solve :: forall i m. MonadBlueprint i a m => m [i]
            solve = toBits ac (highRegisterSize @a @n) (registerSize @a @n)

instance (Arithmetic a, KnownNat n) => ShiftBits (ByteString n ArithmeticCircuit a) where
    shiftBits bs@(ByteString oldBits) s
      | s == 0 = bs
      | Haskell.abs s >= Haskell.fromIntegral (getNatural @n) = false
      | otherwise = ByteString $ circuitN solve
      where
        solve :: forall i m. MonadBlueprint i a m => m (Vector n i)
        solve = do
            bits  <- V.fromVector <$> runCircuit oldBits
            zeros <- replicateM (Haskell.fromIntegral $ Haskell.abs s) $ newAssigned (Haskell.const zero)

            let newBits = case (s < 0) of
                        True  -> take (Haskell.fromIntegral $ getNatural @n) $ zeros <> bits
                        False -> drop (Haskell.fromIntegral s) $ bits <> zeros

            pure $ V.unsafeToVector newBits


    -- | rotateBits does not even require operations on the circuit.
    --
    rotateBits (ByteString bits) s = ByteString (bits { acOutput = V.rotate (acOutput bits) s})


-- | A generic bitwise operation on two ByteStrings.
-- TODO: Shall we expose it to users? Can they do something malicious having such function? AFAIK there are checks that constrain each bit to 0 or 1.
--
bitwiseOperation
    :: forall a n
    .  Arithmetic a
    => ByteString n ArithmeticCircuit a
    -> ByteString n ArithmeticCircuit a
    -> (forall i. i -> i -> ClosedPoly i a)
    -> ByteString n ArithmeticCircuit a
bitwiseOperation (ByteString bits1) (ByteString bits2) cons = ByteString $ circuitN solve
  where
    solve :: forall i m. MonadBlueprint i a m => m (Vector n i)
    solve = do
        varsLeft  <- runCircuit bits1
        varsRight <- runCircuit bits2
        V.zipWithM applyBitwise varsLeft varsRight

    applyBitwise :: forall i m . MonadBlueprint i a m => i -> i -> m i
    applyBitwise l r = newAssigned $ cons l r


instance (Arithmetic a, KnownNat n) => BoolType (ByteString n ArithmeticCircuit a) where
    false = ByteString zero

    true = not false

    not (ByteString bits) = ByteString (flipBits bits)
        where
            flipBits r = circuitN $ do
                is <- runCircuit r
                for is $ \i -> newAssigned (\p -> one - p i)

    l || r = bitwiseOperation l r (\i j x -> x i + x j - x i * x j)

    l && r = bitwiseOperation l r (\i j x -> x i * x j)

    xor l r = bitwiseOperation l r (\i j x -> x i + x j - (x i * x j + x i * x j))


instance
  ( KnownNat wordSize
  , 1 <= wordSize
  , 1 <= n
  , Mod n wordSize ~ 0
  , (Div n wordSize * wordSize) ~ n
  ) => ToWords (ByteString n ArithmeticCircuit a) (ByteString wordSize ArithmeticCircuit a) where

    toWords (ByteString bits) = (\o -> ByteString $ bits { acOutput = o} ) <$> (V.fromVector (V.chunks @(Div n wordSize) @wordSize $ acOutput bits))


instance
  ( Mod n m ~ 0
  , (Div n m * m) ~ n
  , Arithmetic a
  ) => Concat (ByteString m ArithmeticCircuit a) (ByteString n ArithmeticCircuit a) where

    concat bs = ByteString $ bsCircuit `withOutputs` bsOutputs
        where
            bsCircuit = Haskell.mconcat $ (\(ByteString bits) -> acCircuit bits) <$> bs

            bsOutputs :: Vector n Natural
            bsOutputs = V.unsafeConcat @(Div n m) $ (\(ByteString bits) -> acOutput bits) <$> bs

instance
  ( KnownNat n
  , n <= m
  ) => Truncate (ByteString m ArithmeticCircuit a) (ByteString n ArithmeticCircuit a) where

    truncate (ByteString bits) = ByteString $ bits { acOutput = V.take @n (acOutput bits) }

instance
  ( KnownNat m
  , KnownNat n
  , m <= n
  , Arithmetic a
  ) => Extend (ByteString m ArithmeticCircuit a) (ByteString n ArithmeticCircuit a) where

    extend (ByteString oldBits) = ByteString $ circuitN (Vector <$> solve)
      where
        solve :: forall i m'. MonadBlueprint i a m' => m' [i]
        solve = do
            bits <- runCircuit oldBits
            zeros <- replicateM diff $ newAssigned (Haskell.const zero)
            pure $ zeros <> (V.fromVector bits)

        diff :: Haskell.Int
        diff = Haskell.fromIntegral $ getNatural @n Haskell.- getNatural @m
