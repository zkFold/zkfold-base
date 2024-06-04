{-# LANGUAGE AllowAmbiguousTypes          #-}
{-# LANGUAGE DeriveAnyClass               #-}
{-# LANGUAGE DerivingStrategies           #-}
{-# LANGUAGE NoGeneralisedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications             #-}
{-# LANGUAGE TypeOperators                #-}
{-# LANGUAGE UndecidableInstances         #-}

module ZkFold.Symbolic.Data.ByteString
    ( ByteString(..)
    , ShiftBits (..)
    , ToWords (..)
    , Concat (..)
    , Truncate (..)
    ) where

import           Control.DeepSeq                                           (NFData)
import           Control.Monad                                             (mapM, replicateM, zipWithM)
import           Data.Bits                                                 as B
import qualified Data.ByteString                                           as Bytes
import           Data.List                                                 (foldl, reverse, unfoldr)
import           Data.List.Split                                           (chunksOf)
import           Data.Maybe                                                (Maybe (..))
import           Data.Proxy                                                (Proxy (..))
import           Data.String                                               (IsString (..))
import           GHC.Generics                                              (Generic)
import           GHC.Natural                                               (naturalFromInteger)
import           GHC.TypeNats                                              (Mod, Natural, natVal)
import           Prelude                                                   (Bool (..), Integer, drop, error, fmap,
                                                                            length, otherwise, pure, take, type (~),
                                                                            ($), (.), (<$>), (<), (<>), (==), (>=))
import qualified Prelude                                                   as Haskell
import           Test.QuickCheck                                           (Arbitrary (..), chooseInteger)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                           (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Prelude                                            (replicate, replicateA)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint
import           ZkFold.Symbolic.Data.Bool                                 (BoolType (..))
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.UInt


-- | A ByteString which stores @n@ bits and uses elements of @a@ as registers, one element per register.
-- Bit layout is Big-endian.
--
newtype ByteString (n :: Natural) a = ByteString [a]
    deriving (Haskell.Show, Haskell.Eq, Generic, NFData)

instance
    ( FromConstant Natural a
    , Concat (ByteString 7 a) (ByteString n a)
    ) => IsString (ByteString n a) where
    fromString = fromConstant . fromString @Bytes.ByteString

instance
    ( FromConstant Natural a
    , Concat (ByteString 7 a) (ByteString n a)
    ) => FromConstant Bytes.ByteString (ByteString n a) where
    fromConstant bytes = concat
        $ fromConstant @Natural @(ByteString 7 a)
        . Haskell.fromIntegral
        . Haskell.toInteger
        <$> Bytes.unpack bytes

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


instance (ToConstant a Natural) => ToConstant (ByteString n a) Natural where
    toConstant (ByteString bits) = Haskell.foldl (\y p -> toConstant p + base * y) 0 bits
        where base = 2


instance (FromConstant Natural a, KnownNat n) => FromConstant Natural (ByteString n a) where

    -- | Pack a ByteString using one field element per bit.
    -- @fromConstant@ discards bits after @n@.
    -- If the constant is greater than @2^n@, only the part modulo @2^n@ will be converted into a ByteString.
    --
    fromConstant n = ByteString $ reverse bits
        where
            base = 2

            availableBits = unfoldr (toBase base) (n `Haskell.mod` (2 Haskell.^ (getNatural @n))) <> Haskell.repeat (fromConstant @Natural 0)

            bits = take (Haskell.fromIntegral $ value @n) availableBits

-- | Convert a number into @base@-ary system.
--
toBase :: FromConstant Natural a => Natural -> Natural -> Maybe (a, Natural)
toBase _ 0    = Nothing
toBase base b = let (d, m) = b `divMod` base in Just (fromConstant m, d)


instance (FromConstant Natural a, KnownNat n) => FromConstant Integer (ByteString n a) where
    fromConstant = fromConstant . naturalFromInteger . (`Haskell.mod` (2 ^ getNatural @n))

instance (Finite (Zp p), KnownNat n) => Iso (ByteString n (Zp p)) (UInt n (Zp p)) where
    from bs = fromConstant @Natural . toConstant $ bs

instance (Finite (Zp p), KnownNat n) => Iso (UInt n (Zp p)) (ByteString n (Zp p)) where
    from ui = fromConstant @Natural . toConstant $ ui

instance (Finite (Zp p), KnownNat n) => Arbitrary (ByteString n (Zp p)) where
    arbitrary = ByteString <$> replicateA (value @n) (toss (1 :: Natural))
        where toss b = fromConstant <$> chooseInteger (0, 2 ^ b - 1)

instance (Finite (Zp p), KnownNat n) => ShiftBits (ByteString n (Zp p)) where

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


instance (Finite (Zp p), KnownNat n) => BoolType (ByteString n (Zp p)) where
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
  ) => ToWords (ByteString n (Zp p)) (ByteString wordSize (Zp p)) where

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
  ) => Concat (ByteString m (Zp p)) (ByteString n (Zp p)) where

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
  ) => Truncate (ByteString m (Zp p)) (ByteString n (Zp p)) where

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
  ) => Extend (ByteString m (Zp p)) (ByteString n (Zp p)) where

    extend = fromConstant @Natural . toConstant

--------------------------------------------------------------------------------

instance (Arithmetic a, KnownNat n) => SymbolicData a (ByteString n (ArithmeticCircuit a)) where
    pieces (ByteString bits) = bits

    restore bits
      | Haskell.fromIntegral (length bits) == value @n = ByteString bits
      | otherwise = error "ByteString: invalid number of values"

    typeSize = value @n


instance (Arithmetic a, KnownNat n) => Iso (ByteString n (ArithmeticCircuit a)) (UInt n (ArithmeticCircuit a)) where
    from (ByteString bits) =
       case circuits solve of
           (x:xs) -> UInt (Haskell.reverse xs) x
           _      -> error "Iso ByteString UInt : unreachable"
        where
            solve :: forall i m. MonadBlueprint i a m => m [i]
            solve = do
                bsBits <- mapM runCircuit bits
                fromBits (highRegisterSize @a @n) (registerSize @a @n) bsBits

instance (Arithmetic a, KnownNat n) => Iso (UInt n (ArithmeticCircuit a)) (ByteString n (ArithmeticCircuit a)) where
    from (UInt rs r) = ByteString $ circuits solve
        where
            solve :: forall i m. MonadBlueprint i a m => m [i]
            solve = toBits r (Haskell.reverse rs) (highRegisterSize @a @n) (registerSize @a @n)

instance (Arithmetic a, KnownNat n) => ShiftBits (ByteString n (ArithmeticCircuit a)) where
    shiftBits bs@(ByteString oldBits) s
      | s == 0 = bs
      | Haskell.abs s >= Haskell.fromIntegral (getNatural @n) = false
      | otherwise = ByteString $ circuits solve
      where
        solve :: forall i m. MonadBlueprint i a m => m [i]
        solve = do
            bits <- mapM runCircuit oldBits
            zeros <- replicateM (Haskell.fromIntegral $ Haskell.abs s) $ newAssigned (Haskell.const zero)

            pure $ case (s < 0) of
                        True  -> take (Haskell.fromIntegral $ getNatural @n) $ zeros <> bits
                        False -> drop (Haskell.fromIntegral s) $ bits <> zeros


    -- | rotateBits does not even require operations on the circuit.
    --
    rotateBits bs@(ByteString bits) s
      | s == 0 = bs
      | (s < 0) || (s >= intN) = rotateBits bs (s `Haskell.mod` intN) -- Always perform a left rotation
      | otherwise = ByteString $ rotateList bits
      where
        intN :: Integer
        intN = Haskell.fromIntegral (getNatural @n)

        rotateList :: [e] -> [e]
        rotateList lst = drop (Haskell.fromIntegral s) lst <> take (Haskell.fromIntegral s) lst


-- | A generic bitwise operation on two ByteStrings.
-- TODO: Shall we expose it to users? Can they do something malicious having such function? AFAIK there are checks that constrain each bit to 0 or 1.
--
bitwiseOperation
    :: forall a n
    .  Arithmetic a
    => ByteString n (ArithmeticCircuit a)
    -> ByteString n (ArithmeticCircuit a)
    -> (forall i. i -> i -> ClosedPoly i a)
    -> ByteString n (ArithmeticCircuit a)
bitwiseOperation (ByteString bits1) (ByteString bits2) cons = ByteString $ circuits solve
  where
    solve :: forall i m. MonadBlueprint i a m => m [i]
    solve = do
        varsLeft  <- mapM runCircuit bits1
        varsRight <- mapM runCircuit bits2
        zipWithM applyBitwise varsLeft varsRight

    applyBitwise :: forall i m . MonadBlueprint i a m => i -> i -> m i
    applyBitwise l r = newAssigned $ cons l r


instance (Arithmetic a, KnownNat n) => BoolType (ByteString n (ArithmeticCircuit a)) where
    false = ByteString (replicate (value @n) zero)

    true = not false

    not (ByteString bits) = ByteString (flipBits <$> bits)
        where
            flipBits r = circuit $ do
                i <- runCircuit r
                newAssigned (\p -> one - p i)

    l || r = bitwiseOperation l r (\i j x -> x i + x j - x i * x j)

    l && r = bitwiseOperation l r (\i j x -> x i * x j)

    xor l r = bitwiseOperation l r (\i j x -> x i + x j - (x i * x j + x i * x j))


instance
  ( KnownNat wordSize
  , 1 <= wordSize
  , 1 <= n
  , Mod n wordSize ~ 0
  ) => ToWords (ByteString n (ArithmeticCircuit a)) (ByteString wordSize (ArithmeticCircuit a)) where

    toWords (ByteString bits) = ByteString <$> chunksOf (Haskell.fromIntegral $ value @wordSize) bits

instance
  ( Mod n m ~ 0
  ) => Concat (ByteString m (ArithmeticCircuit a)) (ByteString n (ArithmeticCircuit a)) where

    concat bs = ByteString $ Haskell.concatMap (\(ByteString bits) -> bits) bs

instance
  ( KnownNat n
  , n <= m
  ) => Truncate (ByteString m (ArithmeticCircuit a)) (ByteString n (ArithmeticCircuit a)) where

    truncate (ByteString bits) = ByteString $ take (Haskell.fromIntegral $ getNatural @n) bits

instance
  ( KnownNat m
  , KnownNat n
  , m <= n
  , Arithmetic a
  ) => Extend (ByteString m (ArithmeticCircuit a)) (ByteString n (ArithmeticCircuit a)) where

    extend (ByteString oldBits) = ByteString $ circuits solve
      where
        solve :: forall i m'. MonadBlueprint i a m' => m' [i]
        solve = do
            bits <- mapM runCircuit oldBits
            zeros <- replicateM diff $ newAssigned (Haskell.const zero)
            pure $ zeros <> bits

        diff :: Haskell.Int
        diff = Haskell.fromIntegral $ getNatural @n Haskell.- getNatural @m
