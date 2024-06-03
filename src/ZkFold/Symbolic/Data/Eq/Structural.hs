module ZkFold.Symbolic.Data.Eq.Structural where

import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Eq

newtype Structural a = Structural a
-- ^ A newtype wrapper for easy definition of Eq instances.

instance SymbolicData a n x => Eq (Bool (ArithmeticCircuit n a)) (Structural x) where
    Structural x == Structural y =
        let x' = pieces @a x
            y' = pieces y
         in x' == y' 

    Structural x /= Structural y =
        let x' = pieces @a x
            y' = pieces y
         in not (x' == y') 
