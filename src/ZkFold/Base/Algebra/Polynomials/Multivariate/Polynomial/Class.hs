module ZkFold.Base.Algebra.Polynomials.Multivariate.Polynomial.Class where

import           Prelude                           hiding (Num(..), (/), (!!), lcm, length, sum, take, drop)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial

-- | A class for polynomials.
-- `c` is the coefficient type,
-- `i` is the variable type,
-- `j` is the power type.
type Polynomial c i j = (Eq c, Field c, Monomial i j)

--------------------------------- FromPolynomial ---------------------------------

class Polynomial c i j => FromPolynomial c i j m p where
    fromPolynomial :: p -> [(c, M i j m)]

instance Polynomial c i j => FromPolynomial c i j m [(c, M i j m)] where
    fromPolynomial = id

--------------------------------- ToPolynomial -----------------------------------

class Polynomial c i j => ToPolynomial c i j m p where
    toPolynomial   :: [(c, M i j m)] -> Maybe p

instance (Polynomial c i j) => ToPolynomial c i j m [(c, M i j m)] where
    toPolynomial   = Just . filter (\(c, _) -> c /= zero)