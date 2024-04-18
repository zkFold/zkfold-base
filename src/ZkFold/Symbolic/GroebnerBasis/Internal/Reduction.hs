module ZkFold.Symbolic.GroebnerBasis.Internal.Reduction where

import           Data.Bool                                    (bool)
import           Prelude                                      hiding (Num (..), drop, lcm, length, sum, take, (!!), (/))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.GroebnerBasis.Internal.Types

reducable :: (Ord a, MultiplicativeMonoid a) => Polynom a c -> Polynom a c -> Bool
reducable l r = dividable (lt l) (lt r)

reduce :: (Eq c, FiniteField c, Ord a, Ring a) =>
          Polynom a c -> Polynom a c -> Polynom a c
reduce l r = addPoly l r'
    where r' = mulPM r (scale (-1 :: Integer) q)
          q = divideM (lt l) (lt r)

reduceMany :: (Eq c, FiniteField c, Ord a, Ring a) =>
              Polynom a c -> [Polynom a c] -> Polynom a c
reduceMany h fs = if reduced then reduceMany h' fs else h'
    where (h', reduced) = reduceStep h fs False
          reduceStep p (q:qs) r
              | zeroP h   = (h, r)
              | otherwise =
                    if reducable p q
                        then (reduce p q, True)
                        else reduceStep p qs r
          reduceStep p [] r = (p, r)

fullReduceMany :: (Eq c, FiniteField c, Ord a, Ring a) =>
    Polynom a c -> [Polynom a c] -> Polynom a c
fullReduceMany h fs
    | zeroP h'   = h'
    | otherwise = P [lt h'] + fullReduceMany (h' - P [lt h']) fs
    where h' = reduceMany h fs

systemReduce :: (Eq c, FiniteField c, Ord a, Ring a) => [Polynom a c] -> [Polynom a c]
systemReduce = foldr f []
    where f p ps = let p' = fullReduceMany p ps in bool ps (p' : ps) (not $ zeroP p')
