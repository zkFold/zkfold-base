module ZkFold.Base.Algebra.Polynomials.Multivariate.Set where

import           Data.Map                                                (Map)
import           Prelude                                                 hiding (Num (..), length, product, replicate,
                                                                          sum, (!!), (^))

import           ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Polynomial
import           ZkFold.Base.Data.Vector                                 (Vector)

----------------------------- Monomial representations ------------------------------

type MonomialRepAny = Map Integer Integer

type MonomialRepBoundedDegree i d = Vector d (i, Bool)

--------------------------------- Monomial sets -------------------------------------

type MonomialAny = M Integer Integer MonomialRepAny

type MonomialBoundedDegree i d = M i Bool (MonomialRepBoundedDegree i d)

----------------------------- Polynomial representations ----------------------------

type PolynomialRepAny c = [(c, MonomialAny)]

type PolynomialRepBoundedDegree c i d = [(c, MonomialBoundedDegree i d)]

--------------------------------- Polynomial sets -----------------------------------

-- | Most general type for a multivariate polynomial, parameterized by the field of coefficients
type PolynomialAny c = P c Integer Integer MonomialRepAny (PolynomialRepAny c)

-- | Most general type for a multivariate polynomial with bounded degree,
-- parameterized by the field of coefficients, the type of variables, and the degree
type PolynomialBoundedDegree c i d = P c i Bool (MonomialRepBoundedDegree i d) (PolynomialRepBoundedDegree c i d)
