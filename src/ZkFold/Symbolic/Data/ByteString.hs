{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.ByteString
    ( ByteString(..)
    , ShiftBits (..)
    , ToWords (..)
    , Append (..)
    , Truncate (..)
    , Grow (..)
    ) where

import           Control.Monad                                             (forM, mapM, replicateM, zipWithM)
import           Data.Bits                                                 as B
import           Data.List                                                 (concat, foldl, reverse, splitAt, unfoldr)
import           Data.List.Split                                           (chunksOf)
import           Data.Maybe                                                (Maybe (..))
import           Data.Proxy                                                (Proxy (..))
import           GHC.Natural                                               (naturalFromInteger)
import           GHC.TypeNats                                              (KnownNat, Mod, Natural, natVal, type (<=))
import           Prelude                                                   (Bool (..), Integer, divMod, drop, error,
                                                                            fmap, head, length, otherwise, pure, tail,
                                                                            take, type (~), ($), (.), (<$>), (<), (<*>),
                                                                            (<>), (==), (>=))
import qualified Prelude                                                   as Haskell
import           Test.QuickCheck                                           (Arbitrary (..), chooseInteger)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                           (Zp)
import           ZkFold.Prelude                                            (replicate, replicateA)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators    (expansion, horner)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint (ClosedPoly)
import           ZkFold.Symbolic.Data.Bool                                 (BoolType (..))
import           ZkFold.Symbolic.Data.Combinators

data ByteString (n :: Natural) a = ByteString !a ![a]
    deriving (Haskell.Show, Haskell.Eq)

class ShiftBits a where
    {-# MINIMAL (shiftBits | (shiftBitsL, shiftBitsR)), (rotateBits | (rotateBitsL, rotateBitsR)) #-}

    shiftBits :: a -> Integer -> a
    shiftBits a s
      | s < 0     = shiftBitsR a (Haskell.fromIntegral . negate $ s)
      | otherwise = shiftBitsL a (Haskell.fromIntegral s)

    shiftBitsL :: a -> Natural -> a
    shiftBitsL a s = shiftBits a (Haskell.fromIntegral s)

    shiftBitsR :: a -> Natural -> a
    shiftBitsR a s = shiftBits a (negate . Haskell.fromIntegral $ s)

    rotateBits :: a -> Integer -> a
    rotateBits a s
      | s < 0     = rotateBitsR a (Haskell.fromIntegral . negate $ s)
      | otherwise = rotateBitsL a (Haskell.fromIntegral s)

    rotateBitsL :: a -> Natural -> a
    rotateBitsL a s = rotateBits a (Haskell.fromIntegral s)

    rotateBitsR :: a -> Natural -> a
    rotateBitsR a s = rotateBits a (negate . Haskell.fromIntegral $ s)

class ToWords a b where
    toWords :: a -> [b]

class Append a b where
    append :: [a] -> b

class Truncate a b where
    truncate :: a -> b

class Grow a b where
    grow :: a -> b

instance (Finite a, ToConstant a Natural, KnownNat n) => ToConstant (ByteString n a) Natural where
  toConstant (ByteString x xs) = Haskell.foldl (\y p -> toConstant p + base * y) 0 (x:xs)
    where base = 2 Haskell.^ maxBitsPerRegister @a @n

instance (FromConstant Natural a, Finite a, KnownNat n) => FromConstant Natural (ByteString n a) where
  -- | fromConstant discards bits after @n@.
  -- If the constant is greater than 2^@n@, only the part modulo 2^@n@ will be converted into ByteString.
  fromConstant n = case reverse bits of
                     []     -> error "FromConstant: unreachable"
                     (r:rs) -> ByteString r rs
    where
        base = 2 Haskell.^ maxBitsPerRegister @a @n

        availableBits = unfoldr (toBase base) (n `Haskell.mod` (2 Haskell.^ (getNatural @n))) <> Haskell.repeat (fromConstant @Natural 0)

        bits = take (Haskell.fromIntegral $ minNumberOfRegisters @a @n) availableBits

toBase :: FromConstant Natural a => Natural -> Natural -> Maybe (a, Natural)
toBase _ 0    = Nothing
toBase base b = let (d, m) = b `divMod` base in Just (fromConstant m, d)

instance (FromConstant Natural a, Finite a, KnownNat n) => FromConstant Integer (ByteString n a) where
    fromConstant = fromConstant . naturalFromInteger . (`Haskell.mod` (2 Haskell.^ getNatural @n))

instance (KnownNat p, KnownNat n) => Arbitrary (ByteString n (Zp p)) where
    arbitrary = ByteString
        <$> toss (highRegisterBits @(Zp p) @n)
        <*> replicateA (minNumberOfRegisters @(Zp p) @n -! 1) (toss $ maxBitsPerRegister @(Zp p) @n)
        where toss b = fromConstant <$> chooseInteger (0, 2 Haskell.^ b - 1)


-- | TODO: This implementation duplicates that of UInt. Can we merge them somehow?
instance (KnownNat p, KnownNat n) => AdditiveSemigroup (ByteString n (Zp p)) where
    x + y = fromConstant $ toConstant x + (toConstant @_ @Natural) y

instance (KnownNat p, KnownNat n) => ShiftBits (ByteString n (Zp p)) where
    shiftBits b s = fromConstant $ shift (toConstant @_ @Natural b) (Haskell.fromIntegral s) `Haskell.mod` (2 Haskell.^ (getNatural @n))

    -- @Data.Bits.rotate@ works exactly as @Data.Bits.shift@ for @Natural@, we have to rotate bits manually.
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


instance
  ( KnownNat n
  , KnownNat m
  , KnownNat p
  ) => Append (ByteString m (Zp p)) (ByteString n (Zp p)) where

    append = fromConstant @Natural . foldl (\p y -> toConstant y + p `shift` m) 0
        where
            m = Haskell.fromIntegral $ getNatural @m


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

instance
  ( KnownNat m
  , KnownNat n
  , m <= n
  , KnownNat p
  ) => Grow (ByteString m (Zp p)) (ByteString n (Zp p)) where

    grow = fromConstant @Natural . toConstant

--------------------------------------------------------------------------------

toBits
    :: forall n a
    .  Arithmetic a
    => KnownNat n
    => ArithmeticCircuit a
    -> [ArithmeticCircuit a]
    -> (forall i m. MonadBlueprint i a m => m [i])
toBits hi lo = do
    lows <- mapM runCircuit lo
    high <- runCircuit hi

    bitsLow  <- Haskell.concatMap Haskell.reverse <$> mapM (expansion (maxBitsPerRegister @a @n)) lows
    bitsHigh <- Haskell.reverse <$> expansion (highRegisterBits @a @n) high

    pure $ bitsHigh <> bitsLow

fromBits
    :: forall n a
    .  Arithmetic a
    => KnownNat n
    => (forall i m. MonadBlueprint i a m => [i] -> m [i])
fromBits bits = do
    let (bitsHighNew, bitsLowNew) = splitAt (Haskell.fromIntegral $ highRegisterBits @a @n) bits
    let lowVarsNew = chunksOf (Haskell.fromIntegral $ maxBitsPerRegister @a @n) bitsLowNew

    lowsNew <- mapM (horner . Haskell.reverse) lowVarsNew
    highNew <- horner . Haskell.reverse $  bitsHighNew

    pure $ highNew : lowsNew


instance (Arithmetic a, KnownNat n) => Arithmetizable a (ByteString n (ArithmeticCircuit a)) where
    arithmetize (ByteString a as) = forM (a:as) runCircuit

    restore as
      | Haskell.fromIntegral (length as) == minNumberOfRegisters @a @n = ByteString (head as) (tail as)
      | otherwise = error "UInt: invalid number of values"

    typeSize = minNumberOfRegisters @a @n

-- TODO: I really don't like that summation is implemented here and in UInt. Can we do something about it?
--
instance (Arithmetic a, KnownNat n) => AdditiveSemigroup (ByteString n (ArithmeticCircuit a)) where
    ByteString x xs + ByteString y ys =
      case circuits solve of
          []     -> error "ByteString: unreachable"
          (r:rs) -> ByteString r rs
        where
            solve :: MonadBlueprint i a m => m [i]
            solve = do
                bitsL <- Haskell.reverse <$> toBits @n @a x xs
                bitsR <- Haskell.reverse <$> toBits @n @a y ys
                c <- newAssigned (Haskell.const zero)
                bitsSum <- zipWithCarryM sum3 c bitsL bitsR
                fromBits @n @a $ Haskell.reverse bitsSum

            sum3 :: MonadBlueprint i a m => i -> i -> i -> m (i, i)
            sum3 a b c = do
                r' <- newAssigned $ \p -> p a + p b - p a * p b - p a * p b
                r  <- newAssigned $ \p -> p r' + p c - p r' * p c - p r' * p c -- Result bit
                c' <- newAssigned $ \p -> p a * p b + p r' * p c               -- Carry bit
                pure (r, c')


            zipWithCarryM :: MonadBlueprint i a m => (i -> i -> i -> m (i, i)) -> i -> [i] -> [i] -> m [i]
            zipWithCarryM _ _ [] _ = pure []
            zipWithCarryM _ _ _ [] = pure []
            zipWithCarryM f c (a:as) (b:bs) = do
                (r, c') <- f c a b
                (r:) <$> zipWithCarryM f c' as bs

moveBits
    :: forall n a
    .  Arithmetic a
    => KnownNat n
    => ArithmeticCircuit a
    -> [ArithmeticCircuit a]
    -> (forall i m. MonadBlueprint i a m => ([i] -> [i]) -> m [i])
moveBits hi lo processList = do
    bits <- toBits @n @a hi lo

    let newBits = processList bits

    fromBits @n @a newBits


instance (Arithmetic a, KnownNat n) => ShiftBits (ByteString n (ArithmeticCircuit a)) where
    shiftBits bs@(ByteString x xs) s
      | s == 0 = bs
      | Haskell.abs s >= Haskell.fromIntegral (getNatural @n) = false
      | otherwise = case circuits solve of
          []     -> error "ByteString: unreachable"
          (r:rs) -> ByteString r rs
      where
        solve :: forall i m. MonadBlueprint i a m => m [i]
        solve = do
            zeros <- replicateM (Haskell.fromIntegral $ Haskell.abs s) $ newAssigned (Haskell.const zero)

            let shiftList bits = case (s < 0) of
                    True  -> take (Haskell.fromIntegral $ getNatural @n) $ zeros <> bits
                    False -> drop (Haskell.fromIntegral s) $ bits <> zeros

            moveBits @n x xs shiftList


    rotateBits bs@(ByteString x xs) s
      | s == 0 = bs
      | (s < 0) || (s >= intN) = rotateBits bs (s `Haskell.mod` intN) -- Always perform a left rotation
      | otherwise = case circuits solve of
          []     -> error "ByteString: unreachable"
          (r:rs) -> ByteString r rs
      where
        solve :: forall i m. MonadBlueprint i a m => m [i]
        solve = moveBits @n x xs rotateList

        intN :: Integer
        intN = Haskell.fromIntegral (getNatural @n)

        rotateList :: forall e. [e] -> [e]
        rotateList lst = drop (Haskell.fromIntegral s) lst <> take (Haskell.fromIntegral s) lst


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
      (r:rs) -> ByteString r rs
  where
    solve :: forall i m. MonadBlueprint i a m => m [i]
    solve = do
        varsLeft  <- mapM runCircuit xs
        varsRight <- mapM runCircuit ys
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
    false = ByteString zero (replicate (minNumberOfRegisters @a @n -! 1) zero)

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
  , wordSize <= n
  , 1 <= wordSize
  , 1 <= n
  , Mod n wordSize ~ 0
  , Arithmetic a
  ) => ToWords (ByteString n (ArithmeticCircuit a)) (ByteString wordSize (ArithmeticCircuit a)) where

    toWords (ByteString x xs) = bitsToBS <$> chunksOf (Haskell.fromIntegral $ minNumberOfRegisters @a @wordSize) (circuits solve)
      where
        bitsToBS :: [ArithmeticCircuit a] -> ByteString wordSize (ArithmeticCircuit a)
        bitsToBS []     = error "toWords.bitsToBS :: unreachable"
        bitsToBS (r:rs) = ByteString r rs

        solve :: forall i m. MonadBlueprint i a m => m [i]
        solve = do
            bits <- toBits @n @a x xs
            let words = chunksOf (Haskell.fromIntegral $ getNatural @wordSize) bits
            wordsBits <- mapM (fromBits @wordSize @a) words
            pure $ Haskell.concat wordsBits

instance
  ( KnownNat m
  , KnownNat n
  , Arithmetic a
  ) => Append (ByteString m (ArithmeticCircuit a)) (ByteString n (ArithmeticCircuit a)) where

    append bs =
        case circuits solve of
          []     -> error "<+> :: Unreachable"
          (r:rs) -> ByteString r rs
      where
        solve :: forall i m'. MonadBlueprint i a m' => m' [i]
        solve = do
            bits <- mapM (\(ByteString x xs) -> toBits @m @a x xs) bs
            fromBits @n @a $ concat bits

instance
  ( KnownNat m
  , KnownNat n
  , n <= m
  , Arithmetic a
  ) => Truncate (ByteString m (ArithmeticCircuit a)) (ByteString n (ArithmeticCircuit a)) where

    truncate (ByteString x xs) =
        case circuits solve of
          []     -> error "truncate :: Unreachable"
          (r:rs) -> ByteString r rs
      where
        solve :: forall i m'. MonadBlueprint i a m' => m' [i]
        solve = do
            bits <- take (Haskell.fromIntegral $ getNatural @n) <$> toBits @m @a x xs
            fromBits @n @a $ bits

instance
  ( KnownNat m
  , KnownNat n
  , m <= n
  , Arithmetic a
  ) => Grow (ByteString m (ArithmeticCircuit a)) (ByteString n (ArithmeticCircuit a)) where

    grow (ByteString x xs) =
        case circuits solve of
          []     -> error "truncate :: Unreachable"
          (r:rs) -> ByteString r rs
      where
        solve :: forall i m'. MonadBlueprint i a m' => m' [i]
        solve = do
            bits <- toBits @m @a x xs
            zeros <- replicateM diff $ newAssigned (Haskell.const zero)
            fromBits @n @a $ zeros <> bits

        diff :: Haskell.Int
        diff = Haskell.fromIntegral $ getNatural @n Haskell.- getNatural @m
