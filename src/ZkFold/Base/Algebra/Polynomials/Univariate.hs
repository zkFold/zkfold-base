{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Algebra.Polynomials.Univariate where

import           Prelude                           hiding (Num(..), (/), (^), sum, length, replicate, take, drop)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Prelude                    (replicate, length, take, drop)

-------------------------------- Arbitrary degree polynomials --------------------------------

-- TODO: hide constructor
newtype Poly c = P [c]
    deriving (Eq, Show)

toPoly :: (Ring c, Eq c) => [c] -> Poly c
toPoly = removeZeros . P

fromPoly :: Poly c -> [c]
fromPoly (P cs) = cs

instance (Ring c, Eq c) => AdditiveSemigroup (Poly c) where
    P l + P r = removeZeros $ P $ zipWith (+) l r

instance (Ring c, Eq c) => AdditiveMonoid (Poly c) where
    zero = P []

instance (Ring c, Eq c) => AdditiveGroup (Poly c) where
    negate (P cs) = P $ map negate cs

instance (Ring c, Eq c) => MultiplicativeSemigroup (Poly c) where
    P l * P r = removeZeros $ P $ go l r
        where
            go [] _      = []
            go (x:xs) ys = zipWith (+) (map (x *) ys) (zero : go xs ys)

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

-- TODO: hide constructor
newtype PolyVec c size = PV [c]
    deriving (Eq, Show)

toPolyVec :: forall c size . (Ring c, Finite size) => [c] -> PolyVec c size
toPolyVec = addZeros . PV . take (order @size)

fromPolyVec :: PolyVec c size -> [c]
fromPolyVec (PV cs) = cs

poly2vec :: forall c size . (Ring c, Finite size) => Poly c -> PolyVec c size
poly2vec (P cs) = addZeros $ PV $ take (order @size) cs

vec2poly :: (Ring c, Eq c) => PolyVec c size -> Poly c
vec2poly (PV cs) = removeZeros $ P cs

instance Ring c => AdditiveSemigroup (PolyVec c size) where
    PV l + PV r = PV $ zipWith (+) l r

instance (Ring c, Finite size) => AdditiveMonoid (PolyVec c size) where
    zero = PV $ replicate (order @size) zero

instance (Ring c, Finite size) => AdditiveGroup (PolyVec c size) where
    negate (PV cs) = PV $ map negate cs

-- TODO: check for overflow
instance (Ring c, Finite size, Eq c) => MultiplicativeSemigroup (PolyVec c size) where
    l * r = poly2vec $ vec2poly l * vec2poly r

instance (Ring c, Finite size, Eq c) => MultiplicativeMonoid (PolyVec c size) where
    one = PV $ one : replicate (order @size - 1) zero

instance (Field c, Finite size, Eq c) => MultiplicativeGroup (PolyVec c size) where
    invert = undefined

    l / r = poly2vec $ fst $ qr (vec2poly l) (vec2poly r)

scalePV :: Ring c => c -> PolyVec c size -> PolyVec c size
scalePV c (PV as) = PV $ map (*c) as

castPolyVec :: forall c size size' . (Ring c, Finite size, Finite size', Eq c) => PolyVec c size -> PolyVec c size'
castPolyVec (PV cs)
    | order @size <= order @size'            = PV $ cs ++ replicate (order @size' - order @size) zero
    | all (== zero) (drop (order @size') cs) = PV $ take (order @size') cs
    | otherwise = error "castPolyVec: Cannot cast polynomial vector to smaller size!"

polyVecZero :: forall c size . (Ring c, Finite size) => Integer -> PolyVec c size
polyVecZero n = PV $ replicate n zero ++ [one] ++ replicate (order @size - n - 1) zero

polyVecLagrange :: forall c size . (Field c, Eq c, FromConstant Integer c, Finite size) =>
    Integer -> Integer -> c -> PolyVec c size
polyVecLagrange n i omega = scalePV (omega / fromConstant n) $ polyVecZero n / toPolyVec [negate (omega^i), one]

-------------------------------- Helper functions --------------------------------

removeZeros :: (Ring c, Eq c) => Poly c -> Poly c
removeZeros (P cs) = P $ reverse $ go $ reverse cs
    where
        go [] = []
        go (x:xs) = if x == zero then go xs else x:xs

addZeros :: forall c size . (Ring c, Finite size) => PolyVec c size -> PolyVec c size
addZeros (PV cs) = PV $ cs ++ replicate (order @size - length cs) zero