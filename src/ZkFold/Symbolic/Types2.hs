module ZkFold.Symbolic.Types2
  ( Symbolic'
  , SymbolicData'
  , SymbolicFunction
  ) where

import           Data.Foldable                   (Foldable)

import           ZkFold.Base.Algebra.Basic.Class

type Symbolic' a = (FiniteField a, Trichotomy a, BinaryExpansion a)

type SymbolicData' a v = (Symbolic' a, VectorSpace a v, Foldable v)

type SymbolicFunction a f =
  (LinearMap a f, SymbolicData' a (OutputSpace a f))
