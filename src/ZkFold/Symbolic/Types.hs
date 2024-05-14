module ZkFold.Symbolic.Types (Symbolic) where

import           ZkFold.Base.Algebra.Basic.Class  (BinaryExpansion, FiniteField, TrichotomyField)

type Symbolic a = (FiniteField a, BinaryExpansion a, TrichotomyField a)
