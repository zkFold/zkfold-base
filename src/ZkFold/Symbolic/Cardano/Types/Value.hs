{-# LANGUAGE DerivingVia #-}

module ZkFold.Symbolic.Cardano.Types.Value where

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector         (Vector (Vector))
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.UInt       (UInt)

newtype Value size a = Value [(a, a, UInt 32 a)]

deriving via (Vector size (ArithmeticCircuit a, ArithmeticCircuit a, UInt 32 (ArithmeticCircuit a)))
    instance (Arithmetic a, Finite size) => Arithmetizable a (Value size (ArithmeticCircuit a))
