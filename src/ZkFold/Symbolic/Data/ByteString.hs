{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.ByteString
    ( ByteString(..)
    , ShiftBits (..)
    , ToWords (..)
    , Concat (..)
    , Truncate (..)
    , Extend (..)
    ) where

import           Control.DeepSeq                                           (NFData)
import           Control.Monad                                             (forM, mapM, replicateM, zipWithM)
import           Data.Bits                                                 as B
import           Data.List                                                 (foldl, reverse, splitAt, unfoldr)
import           Data.List.Split                                           (chunksOf)
import           Data.Maybe                                                (Maybe (..))
import           Data.Proxy                                                (Proxy (..))
import qualified Data.Vector                                               as V
import           GHC.Generics                                              (Generic)
import           GHC.Natural                                               (naturalFromInteger)
import           GHC.TypeNats                                              (KnownNat, Mod, Natural, natVal, type (<=))
import           Prelude                                                   (Bool (..), Integer, divMod, drop, error,
                                                                            fmap, head, length, null, otherwise, pure,
                                                                            tail, take, type (~), ($), (.), (<$>), (<),
                                                                            (<*>), (<>), (==), (>=))
import qualified Prelude                                                   as Haskell
import           Test.QuickCheck                                           (Arbitrary (..), chooseInteger)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                           (Zp)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators    (expansion, horner)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint
import           ZkFold.Symbolic.Data.Bool                                 (BoolType (..))
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.UInt


-- | A ByteString which stores @n@ bits and uses elements of @a@ as registers.
-- Bit layout is Big-endian. @a@ is the higher register defined separately as it may store less bits than the lower registers.
--
data ByteString (n :: Natural) a = ByteString !a !(V.Vector a)
    deriving (Haskell.Show, Haskell.Eq, Generic, NFData)


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


-- | Describes types that can increase their capacity by adding zero bits to the beginning (i.e. before the higher register).
--
class Extend a b where
    extend :: a -> b

instance (Finite a, ToConstant a Natural, KnownNat n) => ToConstant (ByteString n a) Natural where
    toConstant (ByteString x xs) = Haskell.foldl (\y p -> toConstant p + base * y) 0 (x `V.cons` xs)
        where base = 2 Haskell.^ maxBitsPerRegister @a @n


instance (FromConstant Natural a, Finite a, KnownNat n) => FromConstant Natural (ByteString n a) where

    -- | Pack a ByteString as tightly as possible, allocating the largest possible number of bits to each register.
    -- @fromConstant@ discards bits after @n@.
    -- If the constant is greater than @2^n@, only the part modulo @2^n@ will be converted into a ByteString.
    --
    fromConstant n = case reverse bits of
                        []     -> error "FromConstant: unreachable"
                        (r:rs) -> ByteString r (V.fromList rs)
        where
            base = 2 Haskell.^ maxBitsPerRegister @a @n

            availableBits = unfoldr (toBase base) (n `Haskell.mod` (2 Haskell.^ (getNatural @n))) <> Haskell.repeat (fromConstant @Natural 0)

            bits = take (Haskell.fromIntegral $ minNumberOfRegisters @a @n) availableBits

-- | Convert a number into @base@-ary system.
--
toBase :: FromConstant Natural a => Natural -> Natural -> Maybe (a, Natural)
toBase _ 0    = Nothing
toBase base b = let (d, m) = b `divMod` base in Just (fromConstant m, d)


instance (FromConstant Natural a, Finite a, KnownNat n) => FromConstant Integer (ByteString n a) where
    fromConstant = fromConstant . naturalFromInteger . (`Haskell.mod` (2 ^ getNatural @n))


instance (KnownNat p, KnownNat n) => Iso (ByteString n (Zp p)) (UInt n (Zp p)) where
    from bs@(ByteString r rs)
      | null rs && ((highRegisterSize @(Zp p) @n) >= (getNatural @n)) = UInt V.empty r
      | otherwise = fromConstant @Natural . toConstant $ bs

instance (KnownNat p, KnownNat n) => Iso (UInt n (Zp p)) (ByteString n (Zp p)) where
    from ui@(UInt rs r)
      | null rs = ByteString r rs -- A ByteString's high register always has at least the same capacity as UInt's
      | otherwise = fromConstant @Natural . toConstant $ ui


instance (KnownNat p, KnownNat n) => Arbitrary (ByteString n (Zp p)) where
    arbitrary = ByteString
        <$> toss (highRegisterBits @(Zp p) @n)
        <*> V.replicateM (Haskell.fromIntegral (minNumberOfRegisters @(Zp p) @n -! 1)) (toss $ maxBitsPerRegister @(Zp p) @n)
        where toss b = fromConstant <$> chooseInteger (0, 2 ^ b - 1)


instance (KnownNat p, KnownNat n) => ShiftBits (ByteString n (Zp p)) where
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


instance (KnownNat p, KnownNat n) => BoolType (ByteString n (Zp p)) where
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
  , KnownNat p
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
  , KnownNat p
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
  , KnownNat p
  ) => Truncate (ByteString m (Zp p)) (ByteString n (Zp p)) where

    truncate = fromConstant @Natural . (`shiftR` diff) . toConstant
        where
            diff :: Haskell.Int
            diff = Haskell.fromIntegral $ getNatural @m Haskell.- getNatural @n

-- | Only a smaller ByteString can be extended into a bigger one.
--
instance
  ( KnownNat m
  , KnownNat n
  , m <= n
  , KnownNat p
  ) => Extend (ByteString m (Zp p)) (ByteString n (Zp p)) where

    extend = fromConstant @Natural . toConstant

--------------------------------------------------------------------------------

-- | Convert an @ArithmeticCircuit@ to bits and return their corresponding variables.
--
toBits
    :: forall a
    .  ArithmeticCircuit a
    -> [ArithmeticCircuit a]
    -> Natural
    -> Natural
    -> (forall i m. MonadBlueprint i a m => m [i])
toBits hi lo hiBits loBits = do
    lows <- mapM runCircuit lo
    high <- runCircuit hi

    bitsLow  <- Haskell.concatMap Haskell.reverse <$> mapM (expansion loBits) lows
    bitsHigh <- Haskell.reverse <$> expansion hiBits high

    pure $ bitsHigh <> bitsLow


-- | The inverse of @toBits@.
--
fromBits
    :: forall a
    .  Natural
    -> Natural
    -> (forall i m. MonadBlueprint i a m => [i] -> m [i])
fromBits hiBits loBits bits = do
    let (bitsHighNew, bitsLowNew) = splitAt (Haskell.fromIntegral hiBits) bits
    let lowVarsNew = chunksOf (Haskell.fromIntegral loBits) bitsLowNew

    lowsNew <- mapM (horner . Haskell.reverse) lowVarsNew
    highNew <- horner . Haskell.reverse $  bitsHighNew

    pure $ highNew : lowsNew


instance (Arithmetic a, KnownNat n) => SymbolicData a (ByteString n (ArithmeticCircuit a)) where
    pieces (ByteString a as) = a : V.toList as

    restore as
      | Haskell.fromIntegral (length as) == minNumberOfRegisters @a @n = ByteString (head as) (V.fromList (tail as))
      | otherwise = error "ByteString: invalid number of values"

    typeSize = minNumberOfRegisters @a @n

instance (Arithmetic a, KnownNat n) => Iso (ByteString n (ArithmeticCircuit a)) (UInt n (ArithmeticCircuit a)) where
    from (ByteString r rs)
      | null rs && ((highRegisterSize @a @n) >= (getNatural @n)) = UInt V.empty r
      | otherwise = case circuits solve of
                      (x:xs) -> UInt (V.reverse (V.fromList xs)) x
                      _      -> error "Iso ByteString UInt : unreachable"
        where
            solve :: forall i m. MonadBlueprint i a m => m [i]
            solve = do
                bsBits <- toBits r (V.toList rs) (highRegisterBits @a @n) (maxBitsPerRegister @a @n)
                fromBits (highRegisterSize @a @n) (registerSize @a @n) bsBits

instance (Arithmetic a, KnownNat n) => Iso (UInt n (ArithmeticCircuit a)) (ByteString n (ArithmeticCircuit a)) where
    from (UInt rs r)
      | null rs = ByteString r rs -- A ByteString's high register always has at least the same capacity as UInt's
      | otherwise = case circuits solve of
                      (x:xs) -> ByteString x (V.fromList xs)
                      _      -> error "Iso ByteString UInt : unreachable"
        where
            solve :: forall i m. MonadBlueprint i a m => m [i]
            solve = do
                bsBits <- toBits r (V.toList (V.reverse rs)) (highRegisterSize @a @n) (registerSize @a @n)
                fromBits (highRegisterBits @a @n) (maxBitsPerRegister @a @n) bsBits


-- | Perform some operation on a list of bits.
--
moveBits
    :: forall n a
    .  Arithmetic a
    => KnownNat n
    => ArithmeticCircuit a
    -> [ArithmeticCircuit a]
    -> (forall i m. MonadBlueprint i a m => ([i] -> [i]) -> m [i])
moveBits hi lo processList = do
    bits <- toBits @a hi lo (highRegisterBits @a @n) (maxBitsPerRegister @a @n)

    let newBits = processList bits

    fromBits @a (highRegisterBits @a @n) (maxBitsPerRegister @a @n) newBits


instance (Arithmetic a, KnownNat n) => ShiftBits (ByteString n (ArithmeticCircuit a)) where
    shiftBits bs@(ByteString x xs) s
      | s == 0 = bs
      | Haskell.abs s >= Haskell.fromIntegral (getNatural @n) = false
      | otherwise = case circuits solve of
          []     -> error "ByteString: unreachable"
          (r:rs) -> ByteString r (V.fromList rs)
      where
        solve :: forall i m. MonadBlueprint i a m => m [i]
        solve = do
            zeros <- replicateM (Haskell.fromIntegral $ Haskell.abs s) $ newAssigned (Haskell.const zero)

            let shiftList bits = case (s < 0) of
                    True  -> take (Haskell.fromIntegral $ getNatural @n) $ zeros <> bits
                    False -> drop (Haskell.fromIntegral s) $ bits <> zeros

            moveBits @n x (V.toList xs) shiftList


    rotateBits bs@(ByteString x xs) s
      | s == 0 = bs
      | (s < 0) || (s >= intN) = rotateBits bs (s `Haskell.mod` intN) -- Always perform a left rotation
      | otherwise = case circuits solve of
          []     -> error "ByteString: unreachable"
          (r:rs) -> ByteString r (V.fromList rs)
      where
        solve :: forall i m. MonadBlueprint i a m => m [i]
        solve = moveBits @n x (V.toList xs) rotateList

        intN :: Integer
        intN = Haskell.fromIntegral (getNatural @n)

        rotateList :: forall e. [e] -> [e]
        rotateList lst = drop (Haskell.fromIntegral s) lst <> take (Haskell.fromIntegral s) lst


-- | A generic bitwise operation on two ByteStrings.
-- TODO: Shall we expose it to users? Can they do something malicious having such function? AFAIK there are checks that constrain each bit to 0 or 1.
--
bitwiseOperation
    :: forall a n
    .  Arithmetic a
    => KnownNat n
    => ByteString n (ArithmeticCircuit a)
    -> ByteString n (ArithmeticCircuit a)
    -> (forall i. i -> i -> ClosedPoly i a)
    -> ByteString n (ArithmeticCircuit a)
bitwiseOperation (ByteString x xs) (ByteString y ys) cons =
    case circuits solve of
      []     -> error "ByteString: unreachable"
      (r:rs) -> ByteString r (V.fromList rs)
  where
    solve :: forall i m. MonadBlueprint i a m => m [i]
    solve = do
        varsLeft  <- mapM runCircuit (V.toList xs)
        varsRight <- mapM runCircuit (V.toList ys)
        highLeft  <- runCircuit x
        highRight <- runCircuit y
        lowerRegisters <- zipWithM (applyBitwise False) varsLeft varsRight
        higherRegister <- applyBitwise True highLeft highRight
        pure $ higherRegister : lowerRegisters

    applyBitwise :: forall i m . MonadBlueprint i a m => Bool -> i -> i -> m i
    applyBitwise isHigher l r = do
        bitsL <- expansion regSize l
        bitsR <- expansion regSize r
        resultBits <- zipWithM (\i j -> newAssigned $ cons i j) bitsL bitsR
        horner resultBits
      where
         regSize = case isHigher of
                     False -> maxBitsPerRegister @a @n
                     True  -> highRegisterBits @a @n


instance (Arithmetic a, KnownNat n) => BoolType (ByteString n (ArithmeticCircuit a)) where
    false = ByteString zero (V.replicate (Haskell.fromIntegral (minNumberOfRegisters @a @n -! 1)) zero)

    true = not false

    not (ByteString x xs) = ByteString (flipBits True x) (fmap (flipBits False) xs)
        where
            flipBits isHigher r = circuit $ do
                i <- runCircuit r
                bits <- expansion (if isHigher then highRegisterBits @a @n else maxBitsPerRegister @a @n) i
                flipped <- forM bits $ \b -> newAssigned (\p -> one - p b)
                horner flipped

    l || r = bitwiseOperation l r (\i j x -> x i + x j - x i * x j)

    l && r = bitwiseOperation l r (\i j x -> x i * x j)

    xor l r = bitwiseOperation l r (\i j x -> x i + x j - (x i * x j + x i * x j))


instance
  ( KnownNat wordSize
  , KnownNat n
  , 1 <= wordSize
  , 1 <= n
  , Mod n wordSize ~ 0
  , Arithmetic a
  ) => ToWords (ByteString n (ArithmeticCircuit a)) (ByteString wordSize (ArithmeticCircuit a)) where

    toWords (ByteString x xs) = bitsToBS <$> chunksOf (Haskell.fromIntegral $ minNumberOfRegisters @a @wordSize) (circuits solve)
      where
        bitsToBS :: [ArithmeticCircuit a] -> ByteString wordSize (ArithmeticCircuit a)
        bitsToBS []     = error "toWords.bitsToBS :: unreachable"
        bitsToBS (r:rs) = ByteString r (V.fromList rs)

        solve :: forall i m. MonadBlueprint i a m => m [i]
        solve = do
            bits <- toBits @a x (V.toList xs) (highRegisterBits @a @n) (maxBitsPerRegister @a @n)
            let words = chunksOf (Haskell.fromIntegral $ getNatural @wordSize) bits
            wordsBits <- mapM (fromBits @a (highRegisterBits @a @wordSize) (maxBitsPerRegister @a @wordSize)) words
            pure $ Haskell.concat wordsBits

instance
  ( KnownNat m
  , KnownNat n
  , Mod n m ~ 0
  , Arithmetic a
  ) => Concat (ByteString m (ArithmeticCircuit a)) (ByteString n (ArithmeticCircuit a)) where

    concat bs =
        case circuits solve of
          []     -> error "concat :: Unreachable"
          (r:rs) -> ByteString r (V.fromList rs)
      where
        solve :: forall i m'. MonadBlueprint i a m' => m' [i]
        solve = do
            bits <- mapM (\(ByteString x xs) -> toBits @a x (V.toList xs) (highRegisterBits @a @m) (maxBitsPerRegister @a @m)) bs
            fromBits @a (highRegisterBits @a @n) (maxBitsPerRegister @a @n) $ Haskell.concat bits

instance
  ( KnownNat m
  , KnownNat n
  , n <= m
  , Arithmetic a
  ) => Truncate (ByteString m (ArithmeticCircuit a)) (ByteString n (ArithmeticCircuit a)) where

    truncate (ByteString x xs) =
        case circuits solve of
          []     -> error "truncate :: Unreachable"
          (r:rs) -> ByteString r (V.fromList rs)
      where
        solve :: forall i m'. MonadBlueprint i a m' => m' [i]
        solve = do
            bits <- take (Haskell.fromIntegral $ getNatural @n) <$> toBits @a x (V.toList xs) (highRegisterBits @a @m) (maxBitsPerRegister @a @m)
            fromBits @a (highRegisterBits @a @n) (maxBitsPerRegister @a @n) $ bits

instance
  ( KnownNat m
  , KnownNat n
  , m <= n
  , Arithmetic a
  ) => Extend (ByteString m (ArithmeticCircuit a)) (ByteString n (ArithmeticCircuit a)) where

    extend (ByteString x xs) =
        case circuits solve of
          []     -> error "truncate :: Unreachable"
          (r:rs) -> ByteString r (V.fromList rs)
      where
        solve :: forall i m'. MonadBlueprint i a m' => m' [i]
        solve = do
            bits <- toBits @a x (V.toList xs) (highRegisterBits @a @m) (maxBitsPerRegister @a @m)
            zeros <- replicateM diff $ newAssigned (Haskell.const zero)
            fromBits @a (highRegisterBits @a @n) (maxBitsPerRegister @a @n) $ zeros <> bits

        diff :: Haskell.Int
        diff = Haskell.fromIntegral $ getNatural @n Haskell.- getNatural @m
