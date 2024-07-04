{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- This is what our life will look like from now on if we keep using NumberOfRegisters

module ZkFold.Symbolic.Data.UTCTime where

import           Prelude

import           ZkFold.Symbolic.Compiler                (ArithmeticCircuit)
import           ZkFold.Symbolic.Compiler.Arithmetizable
import           ZkFold.Symbolic.Data.UInt

newtype UTCTime b a = UTCTime (UInt 11 b a)

deriving newtype instance Eq (UInt 11 b a) => Eq (UTCTime b a)

deriving newtype instance Arithmetic a => SymbolicData a (UTCTime ArithmeticCircuit a)
