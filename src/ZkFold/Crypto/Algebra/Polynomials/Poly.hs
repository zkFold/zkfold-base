module ZkFold.Crypto.Algebra.Polynomials.Poly where

import           Prelude                           hiding (Num(..), (/), (!!), lcm, length, sum, take, drop)
import           Data.List                         (intercalate)
import           ZkFold.Crypto.Algebra.Basic.Class

newtype Poly c = P [c]

instance (Show c, Eq c, Field c) => Show (Poly c) where
    show (P cs) = intercalate " + " (map (\ (c, i) -> (if c == one then "" else show c) ++ "x^" ++ show i) $ filter (\(c, _) -> c /= zero) (zip cs [1..]))

instance (Field c) => AdditiveSemigroup (Poly c) where
    P l + P r = addPoly (P l) (P r)

instance (Field c) => MultiplicativeSemigroup (Poly c) where
    P l * P r = mulPoly (P l) (P r)

addPoly :: (Field c) => Poly c -> Poly c -> Poly c
addPoly (P l) (P r) = P (go l r)
    where
          go [] [] = []
          go as [] = as
          go [] bs = bs
          go (a:as) (b:bs) = a + b : go as bs

-- TODO: speed up this, dumb multiplication
mulPoly :: (Field c) => Poly c -> Poly c -> Poly c
mulPoly (P cs) r = foldl (\ s (c, i) -> addPoly (shiftPoly i (mulPolyByConstant c r)) s) (P []) (zip cs [1..])

mulPolyByConstant :: (Field c) => c -> Poly c -> Poly c
mulPolyByConstant l (P cs) = P (map (l *) cs)


shiftPoly :: (Field c) => Int -> Poly c -> Poly c
shiftPoly d (P cs) = P (replicate d zero ++ cs)