{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- This is what our life will look like from now on if we keep using NumberOfRegisters

module ZkFold.Symbolic.Data.UTCTime where

import           GHC.TypeNats                            (KnownNat)
import           Prelude

import           ZkFold.Symbolic.Compiler                (ArithmeticCircuit)
import           ZkFold.Symbolic.Compiler.Arithmetizable
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.UInt

newtype UTCTime a = UTCTime (UInt 11 a)

deriving newtype instance Eq (UInt 11 a) => Eq (UTCTime a)

deriving newtype instance (Arithmetic a, r ~ NumberOfRegisters a 11, KnownNat r) => SymbolicData a r (UTCTime (ArithmeticCircuit r a))
