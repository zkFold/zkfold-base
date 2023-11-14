module ZkFold.Base.Algebra.Polynomials.Univariate where

import           Prelude                           hiding (Num(..), (/), sum, length, replicate)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Prelude                    (replicate, length)

-- | A univariate polynomial of degree `< size` over a field of size q.
newtype Poly c size = P [c]
    deriving (Eq, Show)

toPoly :: (Ring c, Eq c) => [c] -> Poly c size
toPoly = removeZeroTerms . P

instance (Ring c, Eq c) => AdditiveSemigroup (Poly c size) where
    P l + P r = removeZeroTerms $ P $ zipWith (+) l r

instance (Ring c, Eq c) => AdditiveMonoid (Poly c size) where
    zero = P []

instance (Ring c, Eq c) => AdditiveGroup (Poly c size) where
    negate (P cs) = P $ map negate cs

instance (Ring c, Eq c) => MultiplicativeSemigroup (Poly c size) where
    P l * P r = removeZeroTerms $ P $ go l r
        where
            go [] _      = []
            go (x:xs) ys = zipWith (+) (map (x *) ys) (zero : go xs ys)

instance (Ring c, Eq c) => MultiplicativeMonoid (Poly c size) where
    one = P [one]

lt :: Poly c size -> c
lt (P cs) = last cs

deg :: Poly c size -> Integer
deg (P cs) = length cs - 1

scale :: Ring c => c -> Integer -> Poly c size -> Poly c size
scale a n (P cs) = P $ replicate n zero ++ map (a *) cs

qr :: (Field c, Eq c) => Poly c size -> Poly c size -> (Poly c size, Poly c size)
qr a b = go a b zero
    where
        go x y q = if deg x < deg y then (q, x) else go x' y q'
            where
                c = lt x / lt y
                n = deg x - deg y
                x' = x - scale c n y
                q' = q + scale c n one

-- | Extended Euclidean algorithm.
eea :: (Field c, Eq c) => Poly c size -> Poly c size -> (Poly c size, Poly c size)
eea a b = go (a, one) (b, zero)
    where
        go (x, s) (y, t) = if deg y == -1 then (x, s) else go (y, t) (r, s - q * t)
            where
                (q, r) = qr x y

-------------------------------- Helper functions --------------------------------

removeZeroTerms :: (Ring c, Eq c) => Poly c size -> Poly c size
removeZeroTerms (P cs) = P $ reverse $ go $ reverse cs
    where
        go [] = []
        go (x:xs) = if x == zero then go xs else x:xs