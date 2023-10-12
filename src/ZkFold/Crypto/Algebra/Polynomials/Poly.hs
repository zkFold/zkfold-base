module ZkFold.Crypto.Algebra.Polynomials.Poly where

import           ZkFold.Crypto.Algebra.Basic.Class

newtype Poly c = P [c]

addPoly :: (FiniteField c) => Poly c -> Poly c -> Poly c
addPoly (P l) (P r) = P (go l r)
    where
          go [] [] = []
          go as [] = as
          go [] bs = bs
          go (a:as) (b:bs) = a + b : go as bs

instance (FiniteField c) => AdditiveSemigroup (Poly c) where
    P l + P r = addPoly (P l) (P r)