module ZkFold.Symbolic.GroebnerBasis.Types (
    Variable,
    Monomial,
    Polynomial,
    variable,
    monomial,
    polynomial
    ) where

import           Data.List                                    (sortBy)
import           Data.Map                                     (Map)
import           Numeric.Natural                              (Natural)
import           Prelude                                      hiding (Num (..), length, replicate, (!!))

import           ZkFold.Base.Algebra.Basic.Field              (Zp)
import           ZkFold.Base.Algebra.Basic.Number             (Prime)
import           ZkFold.Symbolic.GroebnerBasis.Internal.Types

type Variable p = Var (Zp p) Natural

variable :: Natural -> Variable p
variable = Free

type Monomial p = Monom (Zp p) Natural

monomial :: Zp p -> Map Natural (Variable p) -> Monomial p
monomial = M

type Polynomial p = Polynom (Zp p) Natural

polynomial :: Prime p => [Monomial p] -> Polynomial p
polynomial = P . sortBy (flip compare) . filter (not . zeroM)
