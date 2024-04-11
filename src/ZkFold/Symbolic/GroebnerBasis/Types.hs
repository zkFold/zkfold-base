module ZkFold.Symbolic.GroebnerBasis.Types
  ( Variable,
    Monomial,
    Polynomial,
    variable,
    monomial,
    polynomial,
  )
where

import Data.List (sortBy)
import Data.Map (Map)
import Numeric.Natural (Natural)
import ZkFold.Base.Algebra.Basic.Field (Zp)
import ZkFold.Base.Algebra.Basic.Number (Prime)
import ZkFold.Symbolic.GroebnerBasis.Internal.Types
import Prelude hiding (Num (..), length, replicate, (!!))

type Variable p = Var Integer (Zp p)

variable :: Integer -> Variable p
variable = Free

type Monomial p = Monom Integer (Zp p)

monomial :: Zp p -> Map Natural (Variable p) -> Monomial p
monomial = M

type Polynomial p = Polynom Integer (Zp p)

polynomial :: (Prime p) => [Monomial p] -> Polynomial p
polynomial = P . sortBy (flip compare) . filter (not . zeroM)
