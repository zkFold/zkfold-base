{-# LANGUAGE TypeOperators #-}

module ZkFold.Base.Protocol.Protostar.ArithmetizableFunction where

import           GHC.Generics             (U1 (..), (:*:) (..))

import           ZkFold.Symbolic.Compiler

data ArithmetizableFunction a i p = ArithmetizableFunction
  { afEval    :: i a -> p a -> i a
  , afCircuit :: ArithmeticCircuit a (i :*: p) i U1
  }
