module ZkFold.Crypto.Algebra.Polynomials.Poly where

import           Prelude                           hiding (Num(..), (/), (!!), lcm, length, sum, take, drop)
import           Data.List                         (intercalate)
import           ZkFold.Crypto.Algebra.Basic.Class

newtype Poly c = P [c]

instance (Show c, Eq c, FiniteField c) => Show (Poly c) where
    show (P cs) = intercalate " + " (zipWith (\ c i -> (if c == zero then "" else (if c == one then "" else show c) ++ "x^" ++ show i)) cs [1..])

addPoly :: (FiniteField c) => Poly c -> Poly c -> Poly c
addPoly (P l) (P r) = P (go l r)
    where
          go [] [] = []
          go as [] = as
          go [] bs = bs
          go (a:as) (b:bs) = a + b : go as bs

instance (FiniteField c) => AdditiveSemigroup (Poly c) where
    P l + P r = addPoly (P l) (P r)