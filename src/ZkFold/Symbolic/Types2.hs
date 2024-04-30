module ZkFold.Symbolic.Types2 (Symbolic', SymbolicData') where

import           ZkFold.Base.Algebra.Basic.Class  (BinaryExpansion, FiniteField, Trichotomy, VectorSpace)

type Symbolic' a = (FiniteField a, Trichotomy a, BinaryExpansion a)

type SymbolicData' a v = (Symbolic' a, VectorSpace a v)
