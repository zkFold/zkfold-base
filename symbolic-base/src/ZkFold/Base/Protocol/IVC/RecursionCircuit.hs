module ZkFold.Base.Protocol.IVC.RecursionCircuit where

import           Prelude                            hiding (Num (..), drop, head, replicate, take, zipWith)

import           ZkFold.Base.Protocol.IVC.Predicate (StepFunction)
import           ZkFold.Symbolic.Compiler

-- | Takes a function `f` and returns a Protostar recursion circuit `R`.
ivcRecursionCircuit :: forall a payload input output nx nu .
    StepFunction nx nu -> ArithmeticCircuit a payload input output
ivcRecursionCircuit _ =
    let
    in undefined
