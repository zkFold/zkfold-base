module ZkFold.Symbolic.Types (Symbolic, I, Symbolic', SymbolicData') where

import           Prelude                          (Integer)

import           ZkFold.Base.Algebra.Basic.Class  (BinaryExpansion, FiniteField, Trichotomy, VectorSpace)
import           ZkFold.Symbolic.Data.Bool        (Bool)
import           ZkFold.Symbolic.Data.Conditional (Conditional)
import           ZkFold.Symbolic.Data.Eq          (Eq)
import           ZkFold.Symbolic.Data.Ord         (Ord)

type Symbolic a = (FiniteField a, BinaryExpansion a, Eq (Bool a) a, Ord (Bool a) a, Conditional (Bool a) a)

type I = Integer

type Symbolic' a = (FiniteField a, Trichotomy a, BinaryExpansion a)

type SymbolicData' a v = (Symbolic' a, VectorSpace a v)
