module ZkFold.Symbolic.Types (Symbolic, SymbolicData, SymbolicFunction) where

import           Prelude                               (Traversable)
import           ZkFold.Base.Algebra.Basic.Class       (BinaryExpansion, FiniteField, TrichotomyField)
import           ZkFold.Base.Algebra.Basic.VectorSpace (FunctionSpace, VectorSpace, type InputSpace, type OutputSpace)

type Symbolic a = (FiniteField a, BinaryExpansion a, TrichotomyField a)

type SymbolicData a u = (VectorSpace a u, Traversable u)

type SymbolicFunction a f = (FunctionSpace a f, Traversable (InputSpace a f), Traversable (OutputSpace a f))
