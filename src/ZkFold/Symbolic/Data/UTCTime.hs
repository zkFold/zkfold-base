{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- This is what our life will look like from now on if we keep using NumberOfRegisters

module ZkFold.Symbolic.Data.UTCTime where

import           Prelude

import           ZkFold.Symbolic.Compiler                (ArithmeticCircuit)
import           ZkFold.Symbolic.Compiler.Arithmetizable
import           ZkFold.Symbolic.Data.FieldElement       (FieldElementData)
import           ZkFold.Symbolic.Data.UInt
import           ZkFold.Symbolic.Interpreter             (Interpreter)

newtype UTCTime b = UTCTime (UInt 11 b)

deriving newtype instance Eq (UInt 11 b) => Eq (UTCTime b)

deriving newtype instance Arithmetic a => FieldElementData (Interpreter a) (UTCTime (Interpreter a))

deriving newtype instance Arithmetic a => SymbolicData a (UTCTime (ArithmeticCircuit a))
