module ZkFold.Symbolic.Data.Eq.Structural where

import Data.Function (id)
import Data.List (null, zipWith)
import ZkFold.Symbolic.Compiler
import ZkFold.Symbolic.Data.Bool
import ZkFold.Symbolic.Data.Eq

newtype Structural a = Structural a
-- ^ A newtype wrapper for easy definition of Eq instances.

instance (Arithmetizable a x) => Eq (Bool (ArithmeticCircuit a)) (Structural x) where
  Structural x == Structural y =
    let x' = circuits (arithmetize x) :: [ArithmeticCircuit a]
        y' = circuits (arithmetize y)
        zs = zipWith (==) x' y'
     in if null zs
          then true
          else all1 id zs

  Structural x /= Structural y =
    let x' = circuits (arithmetize x) :: [ArithmeticCircuit a]
        y' = circuits (arithmetize y)
        zs = zipWith (==) x' y'
     in if null zs
          then false
          else not (all1 id zs)
