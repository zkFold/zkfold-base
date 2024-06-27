module ZkFold.Symbolic.Types (Symbolic, I) where

import           Prelude                          (Integer)

import           ZkFold.Base.Algebra.Basic.Class  (FiniteField, FromConstant)
import           ZkFold.Symbolic.Data.Bool        (Bool)
import           ZkFold.Symbolic.Data.Conditional (Conditional)
import           ZkFold.Symbolic.Data.Eq          (Eq)
import           ZkFold.Symbolic.Data.Ord         (Ord)

type Symbolic a = (FromConstant I a, FiniteField a, Eq (Bool a) a, Ord (Bool a) a, Conditional (Bool a) a)

type I = Integer
