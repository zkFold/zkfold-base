module ZkFold.Base.Algebra.Polynomials.Multivariate.Groebner where

import           Data.Bool                                               (bool)
import           Data.List                                               (sortBy)
import           Prelude                                                 hiding (Num (..), drop, lcm, length, sum, take,
                                                                          (!!), (/))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Polynomial
import           ZkFold.Prelude                                          (length, (!!))

reducable :: Polynomial c i j  => Poly c i j -> Poly c i j -> Bool
reducable l r = dividable (lt l) (lt r)

reduce ::
    forall c i j . (Ring j, Polynomial c i j)
    => Poly c i j
    -> Poly c i j
    -> Poly c i j
reduce l r =
    let q = P [(one, lt l / lt r)]
    in l - q * r

reduceMany ::
       forall c i j . (Ring j, Polynomial c i j)
    => Poly c i j
    -> [Poly c i j]
    -> Poly c i j
reduceMany h fs = if reduced then reduceMany h' fs else h'
  where
    (h', reduced) = reduceStep h fs False
    reduceStep p (q:qs) r
      | zeroP p   = (h, r)
      | otherwise =
        if reducable p q
          then (reduce p q, True)
          else reduceStep p qs r
    reduceStep p [] r = (p, r)

fullReduceMany ::
       forall c i j . (Ring j, Polynomial c i j)
    => Poly c i j
    -> [Poly c i j]
    -> Poly c i j
fullReduceMany h fs =
    let h' = reduceMany h fs
    in case h' of
        P []         -> h'
        P ((c, m):_) -> P [(c, m)] + fullReduceMany (h' - P [(c, m)]) fs

systemReduce ::
       forall c i j . (Ring j, Polynomial c i j)
    => [Poly c i j]
    -> [Poly c i j]
systemReduce = foldr f []
    where
        f p ps =
            let p' = fullReduceMany p ps
            in bool ps (p' : ps) (not $ zeroP p')

makeSPoly ::
       (Ring j, Polynomial c i j)
    => Poly c i j
    -> Poly c i j
    -> Poly c i j
makeSPoly l r =
    let M as = gcdM (lt l) (lt r)
        lcm = lcmM (lt l) (lt r)

        ra  = lcm / lt l
        la  = lcm / lt r

        l'  = (one, ra) `scaleM` l
        r'  = (one, la) `scaleM` r
    in if null as
        then zero
        else r' - l'

groebnerStep ::
        (Ring j, Polynomial c i j)
    => [Poly c i j]
    -> [Poly c i j]
groebnerStep ps =
    let n = length ps
        inds = [(i, j) | i <- [0 .. n-!1], j <- [0 .. n-!1], i < j]
        ss   = map (\(i, j) -> makeSPoly (ps !! i) (ps !! j) `reduceMany` ps) inds
        ss'  = filter (not . zeroP) ss
        ps'  = sortBy (flip compare) (ss' ++ ps)
    in systemReduce ps'