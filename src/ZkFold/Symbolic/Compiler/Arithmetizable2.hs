{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Compiler.Arithmetizable2 where

import Data.Either
import Data.Void
import Prelude (($), (.), type (~))
import ZkFold.Base.Algebra.Basic.Class
import ZkFold.Symbolic.Types2 (SymbolicData')
import ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (ArithmeticCircuit)

class Arithmetizable a f where
  arithmetize :: f -> (Inputs a f -> ArithmeticCircuit a) -> Outputs a f -> ArithmeticCircuit a

type family Inputs a f where
  Inputs a (x (ArithmeticCircuit a) -> f) =
    Either (Basis (ArithmeticCircuit a) x) (Inputs a f)
  Inputs a (u (ArithmeticCircuit a)) = Void

type family Outputs a f where
  Outputs a (x (ArithmeticCircuit a) -> f) = Outputs a f
  Outputs a (u (ArithmeticCircuit a)) = Basis (ArithmeticCircuit a) u

instance {-# OVERLAPPABLE #-}
  ( SymbolicData' (ArithmeticCircuit a) u
  , Basis (ArithmeticCircuit a) u ~ Outputs a (u (ArithmeticCircuit a))
  ) => Arithmetizable a (u (ArithmeticCircuit a)) where
    arithmetize c _ = indexV c

instance {-# OVERLAPPING #-}
  ( SymbolicData' (ArithmeticCircuit a) x
  , Arithmetizable a f
  ) => Arithmetizable a (x (ArithmeticCircuit a) -> f) where
    arithmetize f i = arithmetize (f $ tabulateV (i . Left)) (i . Right)
