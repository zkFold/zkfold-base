module ZkFold.Symbolic.GroebnerBasis.Types (
    Variable,
    Monomial,
    Polynomial,
    variable,
    monomial,
    polynomial
    ) where

import           Data.List                         (sortBy)
import           Data.Map                          (Map)
import           Prelude                           hiding (Num(..), (!!), length, replicate)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field   (Zp)
import           ZkFold.Symbolic.GroebnerBasis.Internal.Types

type Variable p = Var (Zp p) Integer

variable :: Integer -> Variable p
variable = Free

type Monomial p = Monom (Zp p) Integer

monomial :: Zp p -> Map Integer (Variable p) -> Monomial p
monomial = M

type Polynomial p = Polynom (Zp p) Integer

polynomial :: Prime p => [Monomial p] -> Polynomial p
polynomial = P . sortBy (flip compare) . filter (not . zeroM)