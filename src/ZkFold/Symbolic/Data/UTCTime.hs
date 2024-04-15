{-# LANGUAGE DerivingStrategies #-}

module ZkFold.Symbolic.Data.UTCTime where

import           Prelude

import           ZkFold.Symbolic.Compiler                (ArithmeticCircuit)
import           ZkFold.Symbolic.Compiler.Arithmetizable
import           ZkFold.Symbolic.Data.UInt

newtype UTCTime a = UTCTime (UInt 11 a)
    deriving Eq

deriving newtype instance Arithmetic a => SymbolicData a (UTCTime (ArithmeticCircuit a))
