{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module ZkFold.Base.Algebra.Polynomials.Multivariate (
    module ZkFold.Base.Algebra.Polynomials.Multivariate.Polynomial,
    module ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial,
    module ZkFold.Base.Algebra.Polynomials.Multivariate.Set,
    module ZkFold.Base.Algebra.Polynomials.Multivariate.Substitution,
    SomeMonomial,
    SomePolynomial,
    monomial,
    polynomial,
    evalPolynomial,
    evalPolynomial',
    substitutePolynomial,
    variables
    ) where

import           Data.Containers.ListUtils       (nubOrd)
import           Data.Map                        (Map, toList, keys)
import           Data.Maybe                      (fromJust)
import           Prelude                         hiding (sum, (^), product, Num(..), (!!), length, replicate)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Scale (Self(..))
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Polynomial
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Set
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Substitution

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

evalMonomial :: forall i j m b . (FromMonomial i j m, Exponent b j) => (i -> b) -> M i j m -> b
evalMonomial f (M m) = product (map (\(i, j) -> f i ^ j) (toList $ fromMonomial @i @j m))

evalPolynomial :: forall c i j m p b . (FromMonomial i j m, FromPolynomial c i j m p, Algebra b c, Exponent b j)
    => (i -> b) -> P c i j m p -> b
evalPolynomial f (P p) = sum $ map (\(c, m) -> scale c (evalMonomial f m)) (fromPolynomial @c @i @j @m @p p)

evalPolynomial' :: forall c i j m p . (FromMonomial i j m, FromPolynomial c i j m p, BinaryExpansion j)
    => (i -> c) -> P c i j m p -> c
evalPolynomial' f = getSelf . evalPolynomial (Self . f)

substitutePolynomial :: forall c i i' j j' m m' p p' . (BinaryExpansion j, FromMonomial i j m, FromPolynomial c i j m p, FromPolynomial c i' j' m' p', m' ~ Map i' j', p' ~ [(c, M i' j' m')])
    => (i -> P c i' j' m' p') -> P c i j m p -> P c i' j' m' p'
substitutePolynomial = evalPolynomial

variables :: forall c i j m p . (FromMonomial i j m, FromPolynomial c i j m p) => P c i j m p -> [i]
variables (P p) = nubOrd $ concatMap (\(_, M m) -> keys (fromMonomial @i @j @m m)) $ fromPolynomial @c @i @j @m @p p
