{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Algebra.Polynomials.Univariate where

import           Prelude                           hiding (Num(..), sum, length, replicate)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Prelude                    (replicate, length)

newtype Poly c size = P [c]
    deriving (Eq, Show)

instance (Eq c, Ord c) => Ord (Poly c size) where
    compare (P l) (P r) = compare l r

instance Ring c => AdditiveSemigroup (Poly c size) where
    P l + P r = P $ zipWith (+) l r

instance (Ring c, Finite size) => AdditiveMonoid (Poly c size) where
    zero = P $ replicate (order @size) zero

instance (Ring c, Finite size) => AdditiveGroup (Poly c size) where
    negate (P cs) = P $ map negate cs

instance Ring c => MultiplicativeSemigroup (Poly c size) where
    P l * P r = P $ map (sum . zipWith (*) r) $ zipWith (++) (replicate (length l) []) (map (replicate (length r)) l)

instance (Ring c, Finite size) => MultiplicativeMonoid (Poly c size) where
    one = P $ one : replicate (order @size - 1) zero