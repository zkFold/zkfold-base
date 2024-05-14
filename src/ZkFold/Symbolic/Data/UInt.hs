{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

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
import           Data.List                                                 (map, unfoldr, zip, zipWith)
import           Data.Map                                                  (fromList, (!))
import           Data.Traversable                                          (for, traverse)
import           Data.Tuple                                                (swap)
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
import           ZkFold.Base.Algebra.Basic.VectorSpace
import           ZkFold.Prelude                                            (drop, length, replicate, replicateA,
                                                                            splitAt, take, (!!))
import           ZkFold.Symbolic.Compiler                                  hiding (forceZero)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators    (expansion, splitExpansion)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Ord
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Types                                     (Symbolic)

-- TODO (Issue #18): hide this constructor
data UInt (n :: Natural) a = UInt ![a] !a
    deriving (Haskell.Show, Haskell.Eq, Haskell.Foldable, Generic, NFData)

instance (FromConstant Natural a, Finite a, AdditiveMonoid a, KnownNat n) => FromConstant Natural (UInt n a) where
    fromConstant = Haskell.fst . cast @a @n . (`Haskell.mod` (2 ^ getNatural @n))

instance (FromConstant Natural a, Finite a, AdditiveMonoid a, KnownNat n) => FromConstant Integer (UInt n a) where
    fromConstant = fromConstant . naturalFromInteger . (`Haskell.mod` (2 ^ getNatural @n))

instance (FromConstant Natural a, Finite a, AdditiveMonoid a, KnownNat n, MultiplicativeSemigroup (UInt n a)) => Scale Natural (UInt n a)

instance (FromConstant Natural a, Finite a, AdditiveMonoid a, KnownNat n, MultiplicativeSemigroup (UInt n a)) => Scale Integer (UInt n a)

instance MultiplicativeMonoid (UInt n a) => Exponent (UInt n a) Natural where
    (^) = natPow

instance VectorSpace a (UInt n) where
    type Basis a (UInt n) = Haskell.Maybe Haskell.Int
    indexV = Haskell.undefined
    tabulateV = Haskell.undefined

cast :: forall a n . (FromConstant Natural a, Finite a, AdditiveMonoid a, KnownNat n) => Natural -> (UInt n a, [a])
cast n =
    let base = 2 ^ registerSize @a @n
        registers = map fromConstant $ flip unfoldr n $ \case
            0 -> Haskell.Nothing
            x -> Haskell.Just (swap $ x `Haskell.divMod` base)
        r = numberOfRegisters @a @n -! 1
     in case greedySplitAt r registers of
        (lo, hi:rest) -> (UInt lo hi, rest)
        (lo, [])      -> (UInt (lo ++ replicate (r -! length lo) zero) zero, [])
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
    => Eq a (UInt n)
    => KnownNat n
    => AdditiveGroup (UInt n a)
    => UInt n a -> UInt n a -> (UInt n a, UInt n a, UInt n a)
eea a b = eea' 1 a b one zero zero one
    where
        iterations :: Natural
        iterations = value @n * 2 + 1

        eea' :: Natural -> UInt n a -> UInt n a -> UInt n a -> UInt n a -> UInt n a -> UInt n a -> (UInt n a, UInt n a, UInt n a)
        eea' iteration oldR r oldS s oldT t
          | iteration Haskell.== iterations = (oldS, oldT, oldR)
          | otherwise =
                if r Haskell.== zero
                then (if Haskell.even iteration then b - oldS else oldS, if Haskell.odd iteration then a - oldT else oldT, oldR)
                else rec
            where
                quotient = oldR `div` r

                rec = eea' (iteration + 1) r (oldR - quotient * r) s (quotient * s + oldS) t (quotient * t + oldT)

--------------------------------------------------------------------------------

instance (Finite (Zp p), KnownNat n) => Eq (Zp p) (UInt n) where
    x == y =
        if toConstant @_ @Natural x Haskell.== toConstant y
        then true
        else false

instance (Finite (Zp p), KnownNat n) => Ord (Zp p) (UInt n) where
    compare x y = case Haskell.compare (toConstant @_ @Natural x) (toConstant y) of
        Haskell.LT -> lt
        Haskell.EQ -> eq
        Haskell.GT -> gt

instance (Finite (Zp p), KnownNat n, KnownNat m, n <= m) => Extend (UInt n (Zp p)) (UInt m (Zp p)) where
    extend = fromConstant @Natural . toConstant

instance (Finite (Zp p), KnownNat n, KnownNat m, m <= n) => Shrink (UInt n (Zp p)) (UInt m (Zp p)) where
    shrink = fromConstant @Natural . toConstant

instance (Finite (Zp p), KnownNat n) => EuclideanDomain (UInt n (Zp p)) where
    divMod n d = let (q, r) = Haskell.divMod (toConstant n :: Natural) (toConstant d :: Natural)
                  in (fromConstant q, fromConstant r)

instance (Finite (Zp p), KnownNat n) => ToConstant (UInt n (Zp p)) Natural where
    toConstant (UInt xs x) = foldr (\p y -> fromZp p + base * y) 0 (xs ++ [x])
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
    arbitrary = UInt
        <$> replicateA (numberOfRegisters @(Zp p) @n -! 1) (toss $ registerSize @(Zp p) @n)
        <*> toss (highRegisterSize @(Zp p) @n)
        where toss b = fromConstant <$> chooseInteger (0, 2 ^ b - 1)

--------------------------------------------------------------------------------

instance (Arithmetic a, KnownNat n) => Eq (ArithmeticCircuit a) (UInt n) where

instance (Arithmetic a, KnownNat n) => Ord (ArithmeticCircuit a) (UInt n) where

instance (Arithmetic a, KnownNat n) => SymbolicData a (UInt n (ArithmeticCircuit a)) where
    pieces (UInt as a) = as ++ [a]

    restore as = case splitAt (numberOfRegisters @a @n -! 1) as of
        (lo, [hi]) -> UInt lo hi
        (_, _)     -> error "UInt: invalid number of values"

    typeSize = numberOfRegisters @a @n

instance (Arithmetic a, KnownNat n, KnownNat m, n <= m) => Extend (UInt n (ArithmeticCircuit a)) (UInt m (ArithmeticCircuit a)) where
    extend (UInt rlows rhi) =
        case numberOfRegisters @a @m -! numberOfRegisters @a @n of
          0    -> UInt rlows rhi
          diff -> UInt (rlows <> [rhi] <> replicate (diff -! 1) zero) zero

instance (Arithmetic a, KnownNat n, KnownNat k, k <= n) => Shrink (UInt n (ArithmeticCircuit a)) (UInt k (ArithmeticCircuit a)) where
    shrink (UInt rlows rhi) =
        case circuits solve of
             (x:xs) -> UInt (Haskell.reverse xs) x
             _      -> error "Iso ByteString UInt : unreachable"
        where
            solve :: forall i m. MonadBlueprint i a m => m [i]
            solve = do
                bsBits <- toBits rhi (Haskell.reverse rlows) (highRegisterSize @a @n) (registerSize @a @n)
                fromBits (highRegisterSize @a @k) (registerSize @a @k) (drop (value @n -! (value @k)) bsBits)

instance (Arithmetic a, KnownNat n) => EuclideanDomain (UInt n (ArithmeticCircuit a)) where
    divMod (UInt rlows rhi) d = ifThenElse (d == _) (zero, zero) (q, r)
        where
            (q, r) = foldl longDivisionStep (zero, zero) [value @n -! 1, value @n -! 2 .. 0]

            numeratorBits :: [ArithmeticCircuit a]
            numeratorBits =
                concatMap (take (registerSize @a @n) . binaryExpansion) rlows <>
                take (highRegisterSize @a @n) (binaryExpansion rhi)

            addBit :: UInt n (ArithmeticCircuit a) -> ArithmeticCircuit a -> UInt n (ArithmeticCircuit a)
            addBit (UInt [] hr) bit         = (UInt [] $ hr + bit)
            addBit (UInt (low:lows) hr) bit = UInt ((low + bit) : lows) hr

            longDivisionStep
                :: (UInt n (ArithmeticCircuit a), UInt n (ArithmeticCircuit a))
                -> Natural
                -> (UInt n (ArithmeticCircuit a), UInt n (ArithmeticCircuit a))
            longDivisionStep (q', r') i =
                let rs = addBit (r' + r') (numeratorBits !! i)
                 in if rs Haskell.>= d then (q' + fromConstant ((2 :: Natural) ^ i), rs - d) else (q', rs)

instance (Arithmetic a, KnownNat n) => AdditiveSemigroup (UInt n (ArithmeticCircuit a)) where
    UInt [] x + UInt [] y = UInt [] $ circuit $ do
        (z, _) <- runCircuit (x + y) >>= splitExpansion (highRegisterSize @a @n) 1
        return z

    UInt (x : xs) z + UInt (y : ys) w =
        let solve :: MonadBlueprint i a m => m [i]
            solve = do
                (i, j) <- runCircuit (x + y) >>= splitExpansion (registerSize @a @n) 1
                (zs, c) <- flip runStateT j $ traverse StateT $
                    zipWith (fullAdder $ registerSize @a @n) xs ys
                (k, _) <- fullAdder (highRegisterSize @a @n) z w c
                return (k : i : zs)

         in case circuits solve of
            (hi : lo) -> UInt lo hi
            []        -> error "UInt: unreachable"

    UInt _ _ + UInt _ _ = error "UInt: unreachable"

instance (Arithmetic a, KnownNat n) => AdditiveMonoid (UInt n (ArithmeticCircuit a)) where
    zero = UInt (replicate (numberOfRegisters @a @n -! 1) zero) zero

instance (Arithmetic a, KnownNat n) => AdditiveGroup (UInt n (ArithmeticCircuit a)) where
    UInt [] x - UInt [] y = UInt [] $ circuit $ do
        i <- runCircuit x
        j <- runCircuit y
        z0 <- newAssigned (\v -> v i - v j + fromConstant (2 ^ registerSize @a @n :: Natural))
        (z, _) <- splitExpansion (highRegisterSize @a @n) 1 z0
        return z

    UInt (x : xs) z - UInt (y : ys) w =
        let t :: a
            t = (one + one) ^ registerSize @a @n - one

            solve :: MonadBlueprint i a m => m [i]
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

            fullSub :: MonadBlueprint i a m => ArithmeticCircuit a -> ArithmeticCircuit a -> i -> m (i, i)
            fullSub xk yk b = do
                d <- runCircuit (xk - yk)
                s <- newAssigned (\v -> v d + v b + fromConstant t)
                splitExpansion (registerSize @a @n) 1 s

         in case circuits solve of
            (hi : lo) -> UInt lo hi
            []        -> error "UInt: unreachable"

    UInt _ _ - UInt _ _ = error "UInt: unreachable"

    negate uint = if uint Haskell.== zero then zero else negate' uint
        where
            negate' (UInt [] x) = UInt [] (negateN (2 ^ highRegisterSize @a @n) x)
            negate' (UInt (x : xs) x') =
                let y = negateN (2 ^ registerSize @a @n) x
                    ys = map (negateN $ 2 ^ registerSize @a @n -! 1) xs
                    y' = negateN (2 ^ highRegisterSize @a @n -! 1) x'
                 in UInt (y : ys) y'

negateN :: Arithmetic a => Natural -> ArithmeticCircuit a -> ArithmeticCircuit a
negateN n r = circuit $ do
    i <- runCircuit r
    newAssigned (\v -> fromConstant n - v i)

instance (Arithmetic a, KnownNat n) => MultiplicativeSemigroup (UInt n (ArithmeticCircuit a)) where
    UInt [] x * UInt [] y = UInt [] $ circuit $ do
        (z, _) <- runCircuit (x * y) >>= splitExpansion (highRegisterSize @a @n) (maxOverflow @a @n)
        return z

    UInt (x : xs) z * UInt (y : ys) w =
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
                p'0 <- foldrM (\k l -> do
                    k' <- newAssigned (\v -> v (cs ! k) * v (ds ! (r -! (k + 1))))
                    newAssigned (\v -> v k' + v l)) c' [0 .. r -! 1]
                (p', _) <- splitExpansion (highRegisterSize @a @n) (maxOverflow @a @n) p'0
                return (p' : p : ps)

         in case circuits solve of
            (hi : lo) -> UInt lo hi
            []        -> error "UInt: unreachable"

    UInt _ _ * UInt _ _ = error "UInt: unreachable"

instance (Arithmetic a, KnownNat n) => MultiplicativeMonoid (UInt n (ArithmeticCircuit a)) where
    one | numberOfRegisters @a @n Haskell.== 1 = UInt [] one
        | otherwise = UInt (one : replicate (numberOfRegisters @a @n -! 2) zero) zero

instance (Arithmetic a, KnownNat n) => Semiring (UInt n (ArithmeticCircuit a))

instance (Arithmetic a, KnownNat n) => Ring (UInt n (ArithmeticCircuit a))

instance (Arithmetic a, KnownNat n) => Arbitrary (UInt n (ArithmeticCircuit a)) where
    arbitrary = UInt
        <$> replicateA (numberOfRegisters @a @n -! 1) (toss $ registerSize @a @n)
        <*> toss (highRegisterSize @a @n)
        where toss b = fromConstant <$> chooseInteger (0, 2 ^ b - 1)

--------------------------------------------------------------------------------

class StrictConv b a where
    strictConv :: b -> a

instance (FromConstant Natural a, Finite a, AdditiveMonoid a, KnownNat n) => StrictConv Natural (UInt n a) where
    strictConv n = case cast @a @n n of
        (x, []) -> x
        (_, _)  -> error "strictConv: overflow"

instance (Finite (Zp p), KnownNat n) => StrictConv (Zp p) (UInt n (Zp p)) where
    strictConv = strictConv . toConstant @_ @Natural

instance (Arithmetic a, KnownNat n, KnownNat (NumberOfBits a), NumberOfBits a <= n) => StrictConv (ArithmeticCircuit a) (UInt n (ArithmeticCircuit a)) where
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


class StrictNum a where
    strictAdd :: a -> a -> a
    strictSub :: a -> a -> a
    strictMul :: a -> a -> a

instance (Finite (Zp p), KnownNat n) => StrictNum (UInt n (Zp p)) where
    strictAdd x y = strictConv $ toConstant x + toConstant @_ @Natural y
    strictSub x y = strictConv $ toConstant x -! toConstant y
    strictMul x y = strictConv $ toConstant x * toConstant @_ @Natural y

instance (Arithmetic a, KnownNat n) => StrictNum (UInt n (ArithmeticCircuit a)) where
    strictAdd (UInt [] x) (UInt [] y) = UInt [] $ circuit $ do
        z <- runCircuit (x + y)
        _ <- expansion (highRegisterSize @a @n) z
        return z

    strictAdd (UInt (x : xs) z) (UInt (y : ys) w) =
        let solve :: MonadBlueprint i a m => m [i]
            solve = do
                (i, j) <- runCircuit (x + y) >>= splitExpansion (registerSize @a @n) 1
                (zs, c) <- flip runStateT j $ traverse StateT $
                    zipWith (fullAdder $ registerSize @a @n) xs ys
                k <- fullAdded z w c
                _ <- expansion (highRegisterSize @a @n) k
                return (k : i : zs)

         in case circuits solve of
            (hi : lo) -> UInt lo hi
            []        -> error "UInt: unreachable"

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

         in case circuits solve of
            (hi : lo) -> UInt lo hi
            []        -> error "UInt: unreachable"

    strictMul (UInt _ _) (UInt _ _) = error "UInt: unreachable"

--------------------------------------------------------------------------------

fullAdder :: MonadBlueprint i a m => Natural -> ArithmeticCircuit a -> ArithmeticCircuit a -> i -> m (i, i)
fullAdder r xk yk c = fullAdded xk yk c >>= splitExpansion r 1

fullAdded :: MonadBlueprint i a m => ArithmeticCircuit a -> ArithmeticCircuit a -> i -> m i
fullAdded xk yk c = do
    i <- runCircuit xk
    j <- runCircuit yk
    k <- newAssigned (\v -> v i + v j)
    newAssigned (\v -> v k + v c)
