{-# LANGUAGE TypeApplications #-}
module ZkFold.Base.Algebra.Polynomials.Multivariate (
    module ZkFold.Base.Algebra.Polynomials.Multivariate.Polynomial,
    module ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial,
    module ZkFold.Base.Algebra.Polynomials.Multivariate.Set,
    SomeMonomial,
    SomePolynomial,
    monomial,
    polynomial,
    evalPolynomial,
    variables
    ) where

import           Data.Containers.ListUtils       (nubOrd)
import           Data.Map                        (Map, toList, keys)
import           Data.Maybe                      (fromJust)
import           Prelude                         hiding (sum, (^), product, Num(..), (!!), length, replicate)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Prelude                  ((!))

import           ZkFold.Base.Algebra.Polynomials.Multivariate.Polynomial
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Set

-- | Most general type for a multivariate monomial
type SomeMonomial = M Integer Integer (Map Integer Integer)

-- | Most general type for a multivariate polynomial
type SomePolynomial c = P c Integer Integer (Map Integer Integer) [(c, M Integer Integer (Map Integer Integer))]

-- | Monomial constructor
monomial :: Monomial i j => Map i j -> M i j (Map i j)
monomial = M . fromJust . toMonomial

-- | Polynomial constructor
polynomial :: Polynomial c i j => [(c, M i j (Map i j))] -> P c i j (Map i j) [(c, M i j (Map i j))]
polynomial = sum . map (\m -> P [m]) . fromJust . toPolynomial

evalMonomial :: forall i j m b . (FromMonomial i j m, Exponent b j) => M i j m -> Map i b -> b
evalMonomial (M m) xs = product (map (\(i, j) -> (xs ! i)^j) (toList $ fromMonomial @i @j m))

evalPolynomial :: forall c i j m p b . (FromMonomial i j m, FromPolynomial c i j m p, Algebra b c, Exponent b j)
    => P c i j m p -> Map i b -> b
evalPolynomial (P p) xs = sum $ map (\(c, m) -> scale c (evalMonomial m xs)) (fromPolynomial @c @i @j @m @p p)

variables :: forall c i j m p . (FromMonomial i j m, FromPolynomial c i j m p) => P c i j m p -> [i]
variables (P p) = nubOrd $ concatMap (\(_, M m) -> keys (fromMonomial @i @j @m m)) $ fromPolynomial @c @i @j @m @p p