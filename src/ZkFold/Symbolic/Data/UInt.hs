{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- Trust me bro

module ZkFold.Symbolic.Data.UInt (
    StrictConv(..),
    StrictNum(..),
    UInt(..),
    toConstant,
    eea
) where

import           Control.Applicative                                       ((<*>))
import           Control.DeepSeq
import           Control.Monad.State                                       (StateT (..))
import           Data.Foldable                                             (foldr, foldrM, for_)
import           Data.Functor                                              ((<$>))
import           Data.Kind                                                 (Type)
import           Data.List                                                 (map, unfoldr, zip, zipWith)
import           Data.Map                                                  (fromList, (!))
import           Data.Traversable                                          (for, traverse)
import           Data.Tuple                                                (swap)
import qualified Data.Zip                                                  as Z
import           GHC.Generics                                              (Generic)
import           GHC.Natural                                               (naturalFromInteger)
import           GHC.TypeNats                                              (Natural)
import           Prelude                                                   (Integer, concatMap, error, flip, foldl,
                                                                            otherwise, return, ($), (++), (.), (<>),
                                                                            (>>=))
import qualified Prelude                                                   as Haskell
import           Test.QuickCheck                                           (Arbitrary (..), chooseInteger)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                           (Zp, fromZp, toZp)
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Data.Vector                                   as V
import           ZkFold.Base.Data.Vector                                   (Vector (..))
import           ZkFold.Prelude                                            (drop, length, replicate, replicateA,
                                                                            splitAt, take, (!!))
import           ZkFold.Symbolic.Compiler                                  hiding (forceZero)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit                (withOutputs)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators    (embedV, expansion, joinCircuits,
                                                                            splitExpansion)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.Eq.Structural
import           ZkFold.Symbolic.Data.Ord

-- TODO (Issue #18): hide this constructor
data family UInt :: Natural -> Type -> Type

data instance UInt (n :: Natural) (Zp p) = UIntZp ![Zp p] !(Zp p)
    deriving (Haskell.Show, Haskell.Eq, Generic, NFData)

data instance UInt (n :: Natural) (ArithmeticCircuit r a) = UIntAc (ArithmeticCircuit r a)
    deriving (Haskell.Show, Generic, NFData)

instance (KnownNat n, Finite (Zp p)) => FromConstant Natural (UInt n (Zp p)) where
    fromConstant c =
        let (lo, hi, _) = cast @(Zp p) @n . (`Haskell.mod` (2 ^ getNatural @n)) $ c
         in UIntZp (fromConstant <$> lo) (fromConstant hi)

instance (KnownNat n, Finite (Zp p)) => FromConstant Integer (UInt n (Zp p)) where
    fromConstant = fromConstant . naturalFromInteger . (`Haskell.mod` (2 ^ getNatural @n))

instance
    ( FromConstant Natural a
    , Arithmetic a
    , KnownNat n
    , KnownNat r
    , r ~ NumberOfRegisters a n
    ) => FromConstant Natural (UInt n (ArithmeticCircuit r a)) where
    fromConstant c =
        let (lo, hi, _) = cast @a @n . (`Haskell.mod` (2 ^ getNatural @n)) $ c
         in UIntAc $ embedV $ Vector $ fromConstant <$> (lo <> [hi])

instance
    ( FromConstant Natural a
    , Arithmetic a
    , KnownNat n
    , KnownNat r
    , r ~ NumberOfRegisters a n
    ) => FromConstant Integer (UInt n (ArithmeticCircuit r a)) where
    fromConstant = fromConstant . naturalFromInteger . (`Haskell.mod` (2 ^ getNatural @n))

instance (FromConstant Natural (UInt n a), Finite a, AdditiveMonoid a, KnownNat n, MultiplicativeSemigroup (UInt n a)) => Scale Natural (UInt n a)

instance (FromConstant Integer (UInt n a), Finite a, AdditiveMonoid a, KnownNat n, MultiplicativeSemigroup (UInt n a)) => Scale Integer (UInt n a)

instance MultiplicativeMonoid (UInt n a) => Exponent (UInt n a) Natural where
    (^) = natPow

cast :: forall a n . (Finite a, KnownNat n) => Natural -> ([Natural], Natural, [Natural])
cast n =
    let base = 2 ^ registerSize @a @n
        registers = flip unfoldr n $ \case
            0 -> Haskell.Nothing
            x -> Haskell.Just (swap $ x `Haskell.divMod` base)
        r = numberOfRegisters @a @n -! 1
     in case greedySplitAt r registers of
        (lo, hi:rest) -> (lo, hi, rest)
        (lo, [])      -> ((lo ++ replicate (r -! length lo) zero), zero, [])
    where
        greedySplitAt 0 xs = ([], xs)
        greedySplitAt _ [] = ([], [])
        greedySplitAt m (x : xs) =
            let (ys, zs) = greedySplitAt (m -! 1) xs
             in (x : ys, zs)

-- | Extended Euclidean algorithm.
-- Exploits the fact that @s_i@ and @t_i@ change signs in turns on each iteration, so it adjusts the formulas correspondingly
-- and never requires signed arithmetic.
-- (i.e. it calculates @x = b - a@ instead of @x = a - b@ when @a - b@ is negative
-- and changes @y - x@ to @y + x@ on the following iteration)
-- This only affects Bezout coefficients, remainders are calculated without changes as they are always non-negative.
--
-- If the algorithm is used to calculate Bezout coefficients,
-- it requires that @a@ and @b@ are coprime, @b@ is not 1 and @a@ is not 0, otherwise the optimisation above is not valid.
--
-- If the algorithm is only used to find @gcd(a, b)@ (i.e. @s@ and @t@ will be discarded), @a@ and @b@ can be arbitrary integers.
--
eea
    :: forall n a
    .  EuclideanDomain (UInt n a)
    => KnownNat n
    => AdditiveGroup (UInt n a)
    => Eq (Bool a) (UInt n a)
    => Conditional (Bool a) (UInt n a, UInt n a, UInt n a)
    => UInt n a -> UInt n a -> (UInt n a, UInt n a, UInt n a)
eea a b = eea' 1 a b one zero zero one
    where
        iterations :: Natural
        iterations = value @n * 2 + 1

        eea' :: Natural -> UInt n a -> UInt n a -> UInt n a -> UInt n a -> UInt n a -> UInt n a -> (UInt n a, UInt n a, UInt n a)
        eea' iteration oldR r oldS s oldT t
          | iteration == iterations = (oldS, oldT, oldR)
          | otherwise = bool @(Bool a) rec (if Haskell.even iteration then b - oldS else oldS, if Haskell.odd iteration then a - oldT else oldT, oldR) (r == zero)
            where
                quotient = oldR `div` r

                rec = eea' (iteration + 1) r (oldR - quotient * r) s (quotient * s + oldS) t (quotient * t + oldT)

--------------------------------------------------------------------------------

instance (Finite (Zp p), KnownNat n, KnownNat m, n <= m) => Extend (UInt n (Zp p)) (UInt m (Zp p)) where
    extend = fromConstant @Natural . toConstant

instance (Finite (Zp p), KnownNat n, KnownNat m, m <= n) => Shrink (UInt n (Zp p)) (UInt m (Zp p)) where
    shrink = fromConstant @Natural . toConstant

instance (Finite (Zp p), KnownNat n) => EuclideanDomain (UInt n (Zp p)) where
    divMod n d = let (q, r) = Haskell.divMod (toConstant n :: Natural) (toConstant d :: Natural)
                  in (fromConstant q, fromConstant r)

instance (Finite (Zp p), KnownNat n) => Eq (Bool (Zp p)) (UInt n (Zp p)) where
    x == y = Bool . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell.== toConstant y
    x /= y = Bool . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell./= toConstant y

instance (Finite (Zp p), KnownNat n) => Ord (Bool (Zp p)) (UInt n (Zp p)) where
    x <= y = Bool . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell.<= toConstant y
    x < y  = Bool . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell.< toConstant y
    x >= y = Bool . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell.>= toConstant y
    x > y  = Bool . toZp . Haskell.fromIntegral . Haskell.fromEnum $ toConstant @_ @Natural x Haskell.> toConstant y
    max x y = fromConstant $ Haskell.max (toConstant @_ @Natural x) (toConstant y)
    min x y = fromConstant $ Haskell.min (toConstant @_ @Natural x) (toConstant y)

instance (Finite (Zp p), KnownNat n) => ToConstant (UInt n (Zp p)) Natural where
    toConstant (UIntZp xs x) = foldr (\p y -> fromZp p + base * y) 0 (xs ++ [x])
        where base = 2 ^ registerSize @(Zp p) @n

instance (Finite (Zp p), KnownNat n) => ToConstant (UInt n (Zp p)) Integer where
    toConstant = Haskell.fromIntegral @Natural . toConstant

instance (Finite (Zp p), KnownNat n) => AdditiveSemigroup (UInt n (Zp p)) where
    x + y = fromConstant $ toConstant x + toConstant @_ @Natural y

instance (Finite (Zp p), KnownNat n) => AdditiveMonoid (UInt n (Zp p)) where
    zero = fromConstant (0 :: Natural)

instance (Finite (Zp p), KnownNat n) => AdditiveGroup (UInt n (Zp p)) where
    x - y = fromConstant $ toConstant x + 2 ^ getNatural @n -! toConstant y
    negate x = fromConstant $ 2 ^ getNatural @n -! toConstant x

instance (Finite (Zp p), KnownNat n) => MultiplicativeSemigroup (UInt n (Zp p)) where
    x * y = fromConstant $ toConstant x * toConstant @_ @Natural y

instance (Finite (Zp p), KnownNat n) => MultiplicativeMonoid (UInt n (Zp p)) where
    one = fromConstant (1 :: Natural)

instance (Finite (Zp p), KnownNat n) => Semiring (UInt n (Zp p))

instance (Finite (Zp p), KnownNat n) => Ring (UInt n (Zp p))

instance (Finite (Zp p), KnownNat n) => Arbitrary (UInt n (Zp p)) where
    arbitrary = UIntZp
        <$> replicateA (numberOfRegisters @(Zp p) @n -! 1) (toss $ registerSize @(Zp p) @n)
        <*> toss (highRegisterSize @(Zp p) @n)
        where toss b = fromConstant <$> chooseInteger (0, 2 ^ b - 1)

--------------------------------------------------------------------------------

type CircuitUInt n a = UInt n (ArithmeticCircuit (NumberOfRegisters a n) a)

instance (Arithmetic a, KnownNat n, KnownNat r, r ~ NumberOfRegisters a n) => SymbolicData a r (UInt n (ArithmeticCircuit r a)) where
    pieces (UIntAc c) = c

    restore c o = UIntAc $ c `withOutputs` o


instance
    ( Arithmetic a
    , KnownNat n
    , KnownNat k
    , KnownNat (to - from)
    , n <= k
    , from ~ NumberOfRegisters a n
    , to ~ NumberOfRegisters a k
    , (from + (to - from)) ~ to
    ) => Extend (UInt n (ArithmeticCircuit from a)) (UInt k (ArithmeticCircuit to a)) where
    extend (UIntAc ac) = UIntAc (circuitN solve)
        where
            solve :: forall i m. MonadBlueprint i a m => m (Vector to i)
            solve = do
                bsBits <- toBits ac (highRegisterSize @a @n) (registerSize @a @n)
                zeros <- replicateA (value @k -! (value @n)) (newAssigned (Haskell.const zero))
                extended <- fromBits (highRegisterSize @a @k) (registerSize @a @k) (zeros <> bsBits)
                return $ Vector extended

instance
    ( Arithmetic a
    , KnownNat n
    , KnownNat k
    , KnownNat to
    , k <= n
    , from ~ NumberOfRegisters a n
    , to ~ NumberOfRegisters a k
    ) => Shrink (UInt n (ArithmeticCircuit from a)) (UInt k (ArithmeticCircuit to a)) where
    shrink (UIntAc ac) = UIntAc (circuitN solve)
        where
            solve :: forall i m. MonadBlueprint i a m => m (Vector to i)
            solve = do
                bsBits <- toBits ac (highRegisterSize @a @n) (registerSize @a @n)
                shrinked <- fromBits (highRegisterSize @a @k) (registerSize @a @k) (drop (value @n -! (value @k)) bsBits)
                return $ Vector shrinked

    {--
instance (Arithmetic a, KnownNat n, KnownNat r, r ~ NumberOfRegisters a n) => EuclideanDomain (UInt n (ArithmeticCircuit r a)) where
    divMod (UIntAc ac) d = bool @(Bool (ArithmeticCircuit 1 a)) (q, r) (zero, zero) (d == zero)
        where
            (q, r) = foldl longDivisionStep (zero, zero) [value @n -! 1, value @n -! 2 .. 0]

            numeratorBits :: [ArithmeticCircuit (NumberOfRegisters a n) a]
            numeratorBits =
                concatMap (take (registerSize @a @n) . binaryExpansion) rlows <>
                take (highRegisterSize @a @n) (binaryExpansion rhi)

            addBit :: CircuitUInt n a -> ArithmeticCircuit (NumberOfRegisters a n) a -> CircuitUInt n a
            addBit (UInt [] hr) bit         = (UInt [] $ hr + bit)
            addBit (UInt (low:lows) hr) bit = UInt ((low + bit) : lows) hr

            longDivisionStep
                :: (CircuitUInt n a, CircuitUInt n a)
                -> Natural
                -> (CircuitUInt n a, CircuitUInt n a)
            longDivisionStep (q', r') i =
                let rs = addBit (r' + r') (numeratorBits !! i)
                 in bool @(Bool (ArithmeticCircuit a)) (q', rs) (q' + fromConstant ((2 :: Natural) ^ i), rs - d) (rs >= d)

instance (Arithmetic a, KnownNat n, KnownNat r, r ~ NumberOfRegisters a n) => Ord (Bool (ArithmeticCircuit 1 a)) (UInt n (ArithmeticCircuit r a)) where
    x <= y = y >= x

    x <  y = y > x

    (UIntAc rs1) >= (UIntAc rs2) =
        circuitGE
            (Haskell.reverse (getBitsBE rs1))
            (Haskell.reverse (getBitsBE rs2))

    (UIntAc rs1) > (UIntAc rs2) =
        circuitGT
            (Haskell.reverse (getBitsBE rs1))
            (Haskell.reverse (getBitsBE rs2))

    max x y = bool @(Bool (ArithmeticCircuit 1 a)) x y $ x < y

    min x y = bool @(Bool (ArithmeticCircuit 1 a)) x y $ x > y

--}

instance (Arithmetic a, KnownNat n, KnownNat r, r ~ NumberOfRegisters a n) => AdditiveSemigroup (UInt n (ArithmeticCircuit r a)) where
    UIntAc x + UIntAc y = UIntAc (circuitN solve)
        where
            solve :: MonadBlueprint i a m => m (Vector r i)
            solve = do
                xs <- runCircuit x
                ys <- runCircuit y
                z <- newAssigned (Haskell.const zero)
                (zs, c) <- flip runStateT z $ traverse StateT $
                    Z.zipWith (fullAdder $ registerSize @a @n) xs ys
                return zs



instance
    ( Arithmetic a
    , KnownNat n
    , KnownNat r
    , KnownNat (r * Order a)
    , KnownNat (Log2 ((r * Order a) - 1) + 1)
    , r ~ NumberOfRegisters a n
    ) => AdditiveMonoid (UInt n (ArithmeticCircuit r a)) where
    zero = UIntAc zero

instance
    ( Arithmetic a
    , KnownNat n
    , KnownNat r
    , KnownNat (r * Order a)
    , KnownNat (Log2 ((r * Order a) - 1) + 1)
    , r ~ NumberOfRegisters a n
    ) => AdditiveGroup (UInt n (ArithmeticCircuit r a)) where
    x - y = x + negate y

{--
        where
            t :: a
            t = (one + one) ^ registerSize @a @n - one

            solve :: MonadBlueprint i a r m => m (Vector r i)
            solve = do
                i <- runCircuit x
                j <- runCircuit y
                s <- newAssigned (\v -> v i - v j + fromConstant (t + one))
                (k, b0) <- splitExpansion (registerSize @a @n) 1 s
                (zs, b) <- flip runStateT b0 $ traverse StateT (zipWith fullSub xs ys)
                d <- runCircuit (z - w)
                s'0 <- newAssigned (\v -> v d + v b + fromConstant t)
                (s', _) <- splitExpansion (highRegisterSize @a @n) 1 s'0
                return (s' : k : zs)

            fullSub :: MonadBlueprint i a r m => i -> i -> i -> m (i, i)
            fullSub xk yk b = do
                d <- newAssigned (\v -> v xk - v yk)
                s <- newAssigned (\v -> v d + v b + fromConstant t)
                splitExpansion (registerSize @a @n) 1 s
--}

    negate (UIntAc x) =
        let y = 2 ^ registerSize @a @n
            ys = replicate (numberOfRegisters @a @n -! 2) (2 ^ registerSize @a @n -! 1)
            y' = 2 ^ highRegisterSize @a @n -! 1
            ns = Vector $ (y : ys) <> [y']
         in UIntAc (negateN ns x)

negateN :: forall a n . (Arithmetic a, KnownNat n) => Vector n Natural -> ArithmeticCircuit n a -> ArithmeticCircuit n a
negateN ns r = circuitN $ do
    is <- runCircuit r
    vars <- for (Z.zip is ns) $ \(i, n) -> newAssigned (\v -> fromConstant n - v i)
    let listVars = V.fromVector vars
        hi = Haskell.last listVars
    (hi', _) <- splitExpansion (highRegisterSize @a @n) 1 hi
    return $ Vector (Haskell.init listVars <> [hi'])

instance (Arithmetic a, KnownNat n, KnownNat r, r ~ NumberOfRegisters a n) => MultiplicativeSemigroup (UInt n (ArithmeticCircuit r a)) where
    UIntAc x * UIntAc y = UIntAc (circuitN solve)
        where
            solve :: MonadBlueprint i a m => m (Vector r i)
            solve = do
                is <- runCircuit x
                js <- runCircuit y
                let cs = fromList $ zip [0..] $ V.fromVector is
                    ds = fromList $ zip [0..] $ V.fromVector js
                    r  = numberOfRegisters @a @n
                -- multiple addends for middle registers
                qs <- for [1 .. r -! 2] $ \k ->
                    for [0 .. k] $ \l ->
                        newAssigned (\v -> v (cs ! l) * v (ds ! (k -! l)))
                -- middle registers
                z <- newAssigned (Haskell.const zero)
                (ps, c') <- flip runStateT z $ for qs $ StateT . \rs c' -> do
                    s <- foldrM (\k l -> newAssigned (\v -> v k + v l)) c' rs
                    splitExpansion (registerSize @a @n) (maxOverflow @a @n) s
                return (Vector ps)


instance
    ( Arithmetic a
    , KnownNat n
    , KnownNat r
    , KnownNat (r - 1)
    , r ~ NumberOfRegisters a n
    , (1 + (r - 1)) ~ r
    ) => MultiplicativeMonoid (UInt n (ArithmeticCircuit r a)) where

    one = UIntAc $ (one :: ArithmeticCircuit 1 a) `joinCircuits` (zero :: ArithmeticCircuit (NumberOfRegisters a n - 1) a)


instance
    ( Arithmetic a
    , KnownNat n
    , KnownNat r
    , KnownNat (r - 1)
    , KnownNat (n * Order a)
    , KnownNat (r * Order a)
    , KnownNat (Log2 ((r * Order a) - 1) + 1)
    , r ~ NumberOfRegisters a n
    , (1 + (r - 1)) ~ r
    ) => Semiring (UInt n (ArithmeticCircuit r a))

instance
    ( Arithmetic a
    , KnownNat n
    , KnownNat r
    , KnownNat (r - 1)
    , KnownNat (n * Order a)
    , KnownNat (r * Order a)
    , KnownNat (Log2 ((r * Order a) - 1) + 1)
    , r ~ NumberOfRegisters a n
    , (1 + (r - 1)) ~ r
    ) => Ring (UInt n (ArithmeticCircuit r a))

deriving via (Structural (CircuitUInt n a))
         instance (Arithmetic a, KnownNat n, KnownNat r, r ~ NumberOfRegisters a n) =>
         Eq (Bool (ArithmeticCircuit 1 a)) (UInt n (ArithmeticCircuit r a))

instance (Arithmetic a, KnownNat n, KnownNat r, r ~ NumberOfRegisters a n) => Arbitrary (UInt n (ArithmeticCircuit r a)) where
    arbitrary = do
        lows <- replicateA (numberOfRegisters @a @n -! 1) (toss $ registerSize @a @n)
        hi <- toss (highRegisterSize @a @n)
        return $ UIntAc $ embedV (Vector $ lows <> [hi])
        where
            toss b = fromConstant <$> chooseInteger (0, 2 ^ b - 1)


--------------------------------------------------------------------------------

class StrictConv b a where
    strictConv :: b -> a

instance (Finite (Zp p), KnownNat n) => StrictConv Natural (UInt n (Zp p)) where
    strictConv n = case cast @(Zp p) @n n of
        (lo, hi, []) -> UIntZp (toZp . Haskell.fromIntegral <$> lo) (toZp . Haskell.fromIntegral $ hi)
        _            -> error "strictConv: overflow"

instance (FromConstant Natural a, Arithmetic a, KnownNat n, KnownNat r, r ~ NumberOfRegisters a n) => StrictConv Natural (UInt n (ArithmeticCircuit r a)) where
    strictConv n = case cast @a @n n of
        (lo, hi, []) -> UIntAc $ embedV $ Vector $ fromConstant <$> (lo <> [hi])
        _            -> error "strictConv: overflow"

instance (Finite (Zp p), KnownNat n) => StrictConv (Zp p) (UInt n (Zp p)) where
    strictConv = strictConv . toConstant @_ @Natural

{--
instance (Arithmetic a, KnownNat n, KnownNat (NumberOfBits a), NumberOfBits a <= n) => StrictConv (ArithmeticCircuit a) (CircuitUInt n a) where
    strictConv a =
        let (lo, hi) = unsnoc $ take (numberOfRegisters @a @n) $
                            flip unfoldr a $ Haskell.Just . expand
         in UInt lo hi
        where
            unsnoc []       = error "unsnoc: empty list"
            unsnoc [x]      = ([], x)
            unsnoc (x : xs) = let (ys, z) = unsnoc xs in (x : ys, z)

            bitSize = numberOfBits @a
            regSize = registerSize @a @n

            expand :: ArithmeticCircuit a -> (ArithmeticCircuit a, ArithmeticCircuit a)
            expand x = case circuits $ do
                i <- runCircuit x
                (j, k) <- splitExpansion regSize (bitSize -! regSize) i
                return [j, k]
              of
                [y, z] -> (y, z)
                _      -> error "expand: impossible"

--}

class StrictNum a where
    strictAdd :: a -> a -> a
    strictSub :: a -> a -> a
    strictMul :: a -> a -> a

instance (Finite (Zp p), KnownNat n) => StrictNum (UInt n (Zp p)) where
    strictAdd x y = strictConv $ toConstant x + toConstant @_ @Natural y
    strictSub x y = strictConv $ toConstant x -! toConstant y
    strictMul x y = strictConv $ toConstant x * toConstant @_ @Natural y

{--
instance (Arithmetic a, KnownNat n) => StrictNum (CircuitUInt n a) where
    strictAdd (UIntAc x) (UIntAc y) = UIntAc (circuitN solve)
        where
            solve :: MonadBlueprint i a (NumberOfRegisters a n) m => m [i]
            solve = do
                (i, j) <- runCircuit (x + y) >>= splitExpansion (registerSize @a @n) 1
                (zs, c) <- flip runStateT j $ traverse StateT $
                    zipWith (fullAdder $ registerSize @a @n) xs ys
                k <- fullAdded z w c
                _ <- expansion (highRegisterSize @a @n) k
                return (k : i : zs)


    strictAdd (UInt _ _) (UInt _ _) = error "UInt: unreachable"

    strictSub (UInt [] x) (UInt [] y) = UInt [] $ circuit $ do
        z <- runCircuit (x - y)
        _ <- expansion (highRegisterSize @a @n) z
        return z

    strictSub (UInt (x : xs) z) (UInt (y : ys) w) =
        let t :: a
            t = (one + one) ^ registerSize @a @n - one

            solve :: MonadBlueprint i a m => m [i]
            solve = do
                i <- runCircuit x
                j <- runCircuit y
                s <- newAssigned (\v -> v i - v j + fromConstant (t + one))
                (k, b0) <- splitExpansion (registerSize @a @n) 1 s
                (zs, b) <- flip runStateT b0 $ traverse StateT (zipWith fullSub xs ys)
                k' <- runCircuit (z - w)
                s' <- newAssigned (\v -> v k' + v b - one)
                _ <- expansion (highRegisterSize @a @n) s'
                return (s' : k : zs)

            fullSub :: MonadBlueprint i a m => ArithmeticCircuit a -> ArithmeticCircuit a -> i -> m (i, i)
            fullSub xk yk b = do
                k <- runCircuit (xk - yk)
                s <- newAssigned (\v -> v k + v b + fromConstant t)
                splitExpansion (registerSize @a @n) 1 s

         in case circuits solve of
            (hi : lo) -> UInt lo hi
            []        -> error "UInt: unreachable"

    strictSub (UInt _ _) (UInt _ _) = error "UInt: unreachable"

    strictMul (UInt [] x) (UInt [] y) = UInt [] $ circuit $ do
        z <- runCircuit (x * y)
        _ <- expansion (highRegisterSize @a @n) z
        return z

    strictMul (UInt (x : xs) z) (UInt (y : ys) w) =
        let solve :: MonadBlueprint i a m => m [i]
            solve = do
                i <- runCircuit x
                j <- runCircuit y
                is <- for xs runCircuit
                js <- for ys runCircuit
                i' <- runCircuit z
                j' <- runCircuit w
                let cs = fromList $ zip [0..] (i : is ++ [i'])
                    ds = fromList $ zip [0..] (j : js ++ [j'])
                    r  = numberOfRegisters @a @n
                -- single addend for lower register
                q <- newAssigned (\v -> v i * v j)
                -- multiple addends for middle registers
                qs <- for [1 .. r -! 2] $ \k ->
                    for [0 .. k] $ \l ->
                        newAssigned (\v -> v (cs ! l) * v (ds ! (k -! l)))
                -- lower register
                (p, c) <- splitExpansion (registerSize @a @n) (registerSize @a @n) q
                -- middle registers
                (ps, c') <- flip runStateT c $ for qs $ StateT . \rs c' -> do
                    s <- foldrM (\k l -> newAssigned (\v -> v k + v l)) c' rs
                    splitExpansion (registerSize @a @n) (maxOverflow @a @n) s
                -- high register
                p' <- foldrM (\k l -> do
                    k' <- newAssigned (\v -> v (cs ! k) * v (ds ! (r -! (k + 1))))
                    newAssigned (\v -> v l + v k')) c' [0 .. r -! 1]
                _ <- expansion (highRegisterSize @a @n) p'
                -- all addends higher should be zero
                for_ [r .. r * 2 -! 2] $ \k ->
                    for_ [k -! r + 1 .. r -! 1] $ \l ->
                        constraint (\v -> v (cs ! l) * v (ds ! (k -! l)))
                return (p' : p : ps)
--}

--------------------------------------------------------------------------------

fullAdder :: MonadBlueprint i a m => Natural -> i -> i -> i -> m (i, i)
fullAdder r xk yk c = fullAdded xk yk c >>= splitExpansion r 1

fullAdded :: MonadBlueprint i a m => i -> i -> i -> m i
fullAdded i j c = do
    k <- newAssigned (\v -> v i + v j)
    newAssigned (\v -> v k + v c)
