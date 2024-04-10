{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Algebra.Polynomials.Multivariate (
    module ZkFold.Base.Algebra.Polynomials.Multivariate.Polynomial,
    module ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial,
    module ZkFold.Base.Algebra.Polynomials.Multivariate.Set,
    module ZkFold.Base.Algebra.Polynomials.Multivariate.Substitution,
    SomeMonomial,
    SomePolynomial,
    mapCoeffs,
    monomial,
    polynomial,
    evalPolynomial,
    var,
    variables
    ) where

import           Data.Bifunctor                                            (first)
import           Data.Containers.ListUtils                                 (nubOrd)
import           Data.Map                                                  (Map, keys, singleton, toList)
import           Data.Maybe                                                (fromJust)
import           Numeric.Natural                                           (Natural)
import           Prelude                                                   hiding (Num (..), length, product, replicate, sum, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Polynomial
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Set
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Substitution

-- | Most general type for a multivariate monomial
type SomeMonomial = M Natural Natural (Map Natural Natural)

-- | Most general type for a multivariate polynomial
type SomePolynomial c = P c Natural Natural (Map Natural Natural) [(c, M Natural Natural (Map Natural Natural))]

-- | Monomial constructor
monomial :: Monomial i j => Map i j -> M i j (Map i j)
monomial = M . fromJust . toMonomial

-- | Polynomial constructor
polynomial :: Polynomial c i j => [(c, M i j (Map i j))] -> P c i j (Map i j) [(c, M i j (Map i j))]
polynomial = sum . map (\m -> P [m]) . fromJust . toPolynomial

-- | @'var' i@ is a polynomial \(p(x) = x_i\)
var :: Polynomial c i j => i -> P c i j (Map i j) [(c, M i j (Map i j))]
var x = polynomial [(one, monomial (singleton x one))]

evalMonomial :: forall i j m b . (FromMonomial i j m, MultiplicativeMonoid b, Exponent b j) => (i -> b) -> M i j m -> b
evalMonomial f (M m) = product (map (\(i, j) -> f i ^ j) (toList $ fromMonomial @i @j m))

evalPolynomial :: forall c i j m p b . (FromMonomial i j m, FromPolynomial c i j m p, Algebra c b, Exponent b j)
    => (i -> b) -> P c i j m p -> b
evalPolynomial f (P p) = sum $ map (\(c, m) -> scale c (evalMonomial f m)) (fromPolynomial @c @i @j @m @p p)

variables :: forall c i j m p . (FromMonomial i j m, FromPolynomial c i j m p) => P c i j m p -> [i]
variables (P p) = nubOrd $ concatMap (\(_, M m) -> keys (fromMonomial @i @j @m m)) $ fromPolynomial @c @i @j @m @p p

mapCoeffs :: forall c c' i j m p p' . (FromPolynomial c i j m p, ToPolynomial c' i j m p')
    => (c -> c') -> P c i j m p -> P c' i j m p'
mapCoeffs f (P p) = P . fromJust . toPolynomial $ map (first f) (fromPolynomial @c @i @j @m p)
