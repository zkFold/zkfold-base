{-# LANGUAGE DerivingVia #-}
module ZkFold.Symbolic.Cardano.Types.Address where

import           Prelude                            hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool          (Bool)
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Eq            (Eq)
import           ZkFold.Symbolic.Data.Eq.Structural

newtype Address a = Address (ByteString 4 a, (ByteString 224 a, ByteString 224 a))

deriving instance Arithmetic a => SymbolicData a (Address (ArithmeticCircuit a))

deriving via (Structural (Address (ArithmeticCircuit a)))
         instance Arithmetic a =>
         Eq (Bool (ArithmeticCircuit a)) (Address (ArithmeticCircuit a))

paymentCredential :: Address a -> ByteString 224 a
paymentCredential (Address (_, (pc, _))) = pc