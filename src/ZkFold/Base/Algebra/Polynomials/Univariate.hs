{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Base.Algebra.Polynomials.Univariate where

import           Prelude                           hiding (Num(..), (/), (^), sum, product, length, replicate, take, drop)
import           Test.QuickCheck                   (Arbitrary(..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Prelude                    (replicate, length, take, drop, zipWithDefault)

-------------------------------- Arbitrary degree polynomials --------------------------------

-- TODO (Issue #17): hide constructor
newtype Poly c = P [c]
    deriving (Eq, Show)

toPoly :: (Ring c, Eq c) => [c] -> Poly c
toPoly = removeZeros . P

fromPoly :: Poly c -> [c]
fromPoly (P cs) = cs

instance (Ring c, Eq c) => AdditiveSemigroup (Poly c) where
    P l + P r = removeZeros $ P $ zipWithDefault (+) zero zero l r

instance (Ring c, Eq c) => AdditiveMonoid (Poly c) where
    zero = P []

instance (Ring c, Eq c) => AdditiveGroup (Poly c) where
    negate (P cs) = P $ map negate cs

instance (Ring c, Eq c) => MultiplicativeSemigroup (Poly c) where
    P l * P r = removeZeros $ P $ go l r
        where
            go [] _      = []
            go (x:xs) ys = zipWithDefault (+) zero zero (map (x *) ys) (zero : go xs ys)

instance (Ring c, Eq c) => MultiplicativeMonoid (Poly c) where
    one = P [one]

lt :: Poly c -> c
lt (P cs) = last cs

deg :: Poly c -> Integer
deg (P cs) = length cs - 1

scaleP :: Ring c => c -> Integer -> Poly c -> Poly c
scaleP a n (P cs) = P $ replicate n zero ++ map (a *) cs

qr :: (Field c, Eq c) => Poly c -> Poly c -> (Poly c, Poly c)
qr a b = go a b zero
    where
        go x y q = if deg x < deg y then (q, x) else go x' y q'
            where
                c = lt x / lt y
                n = deg x - deg y
                x' = x - scaleP c n y
                q' = q + scaleP c n one

-- | Extended Euclidean algorithm.
eea :: (Field c, Eq c) => Poly c -> Poly c -> (Poly c, Poly c)
eea a b = go (a, one) (b, zero)
    where
        go (x, s) (y, t) = if deg y == -1 then (x, s) else go (y, t) (r, s - q * t)
            where
                (q, r) = qr x y

---------------------------------- Fixed degree polynomials ----------------------------------

-- TODO (Issue #17): hide constructor
newtype PolyVec c size = PV [c]
    deriving (Eq, Show)

toPolyVec :: forall c size . (Ring c, Finite size) => [c] -> PolyVec c size
toPolyVec = PV . take (order @size) . addZeros @c @size

fromPolyVec :: PolyVec c size -> [c]
fromPolyVec (PV cs) = cs

poly2vec :: forall c size . (Ring c, Finite size) => Poly c -> PolyVec c size
poly2vec (P cs) = toPolyVec cs

vec2poly :: (Ring c, Eq c) => PolyVec c size -> Poly c
vec2poly (PV cs) = removeZeros $ P cs

instance Ring c => AdditiveSemigroup (PolyVec c size) where
    PV l + PV r = PV $ zipWith (+) l r

instance (Ring c, Finite size) => AdditiveMonoid (PolyVec c size) where
    zero = PV $ replicate (order @size) zero

instance (Ring c, Finite size) => AdditiveGroup (PolyVec c size) where
    negate (PV cs) = PV $ map negate cs

-- TODO (Issue #18): check for overflow
instance (Ring c, Finite size, Eq c) => MultiplicativeSemigroup (PolyVec c size) where
    l * r = poly2vec $ vec2poly l * vec2poly r

instance (Ring c, Finite size, Eq c) => MultiplicativeMonoid (PolyVec c size) where
    one = PV $ one : replicate (order @size - 1) zero

instance (Field c, Finite size, Eq c) => MultiplicativeGroup (PolyVec c size) where
    invert = undefined

    l / r = poly2vec $ fst $ qr (vec2poly l) (vec2poly r)

instance (Ring c, Arbitrary c, Finite size) => Arbitrary (PolyVec c size) where
    arbitrary = toPolyVec <$> mapM (const arbitrary) [1..order @size]

-- p(x) = a0 + a1 * x
polyVecLinear :: forall c size . (Ring c, Finite size) => c -> c -> PolyVec c size
polyVecLinear a0 a1 = PV $ a0 : a1 : replicate (order @size - 2) zero

-- p(x) = a0 + a1 * x + a2 * x^2
polyVecQuadratic :: forall c size . (Ring c, Finite size) => c -> c -> c -> PolyVec c size
polyVecQuadratic a0 a1 a2 = PV $ a0 : a1 : a2 : replicate (order @size - 3) zero

scalePV :: Ring c => c -> PolyVec c size -> PolyVec c size
scalePV c (PV as) = PV $ map (*c) as

evalPolyVec :: Ring c => PolyVec c size -> c -> c
evalPolyVec (PV cs) x = sum $ zipWith (*) cs $ map (x^) [0 :: Integer ..]

castPolyVec :: forall c size size' . (Ring c, Finite size, Finite size', Eq c) => PolyVec c size -> PolyVec c size'
castPolyVec (PV cs)
    | order @size <= order @size'            = toPolyVec cs
    | all (== zero) (drop (order @size') cs) = toPolyVec cs
    | otherwise = error "castPolyVec: Cannot cast polynomial vector to smaller size!"

-- p(x) = x^n - 1
polyVecZero :: forall c size size' . (Ring c, Finite size, Finite size', Eq c) => PolyVec c size'
polyVecZero = poly2vec $ scaleP one (order @size) one - one

-- L_i(x) : p(omega^i) = 1, p(omega^j) = 0, j /= i, 1 <= i <= n, 1 <= j <= n
polyVecLagrange :: forall c size size' . (Field c, Eq c, FromConstant Integer c, Finite size, Finite size') =>
    Integer -> c -> PolyVec c size'
polyVecLagrange i omega = scalePV (omega^i / fromConstant (order @size)) $ (polyVecZero @c @size @size' - one) / polyVecLinear (negate $ omega^i) one

-- p(x) = c_1 * L_1(x) + c_2 * L_2(x) + ... + c_n * L_n(x)
polyVecInLagrangeBasis :: forall c size size' . (Field c, Eq c, FromConstant Integer c, Finite size, Finite size') =>
    c -> PolyVec c size -> PolyVec c size'
polyVecInLagrangeBasis omega (PV cs) =
    let ls = map (\i -> polyVecLagrange @c @size @size' i omega) [1..]
    in sum $ zipWith scalePV cs ls

polyVecGrandProduct :: forall c size . (Field c, Finite size) =>
    PolyVec c size -> PolyVec c size -> PolyVec c size -> c -> c -> PolyVec c size
polyVecGrandProduct (PV as) (PV bs) (PV sigmas) beta gamma =
    let ps = map (+ gamma) (zipWith (+) as (map (* beta) bs))
        qs = map (+ gamma) (zipWith (+) as (map (* beta) sigmas))
        zs = map (product . flip take (zipWith (/) ps qs)) [0..order @size - 1]
    in PV zs

-------------------------------- Helper functions --------------------------------

removeZeros :: (Ring c, Eq c) => Poly c -> Poly c
removeZeros (P cs) = P $ reverse $ go $ reverse cs
    where
        go [] = []
        go (x:xs) = if x == zero then go xs else x:xs

addZeros :: forall c size . (Ring c, Finite size) => [c] -> [c]
addZeros cs = cs ++ replicate (order @size - length cs) zero