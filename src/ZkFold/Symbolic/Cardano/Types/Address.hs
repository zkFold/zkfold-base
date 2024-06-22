{-# LANGUAGE DerivingVia #-}
module ZkFold.Symbolic.Cardano.Types.Address where

import           Prelude                            hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool          (Bool)
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Eq            (Eq)
import           ZkFold.Symbolic.Data.Eq.Structural

type AddressType a = ByteString 4 a
type PaymentCredential a = ByteString 224 a
type StakingCredential a = ByteString 224 a

newtype Address a = Address (AddressType a, (PaymentCredential a, StakingCredential a))

deriving instance Arithmetic a => SymbolicData a (Address (ArithmeticCircuit a))

deriving via (Structural (Address (ArithmeticCircuit a)))
         instance Arithmetic a =>
         Eq (Bool (ArithmeticCircuit a)) (Address (ArithmeticCircuit a))

addressType :: Address a -> AddressType a
addressType (Address (t, _)) = t

paymentCredential :: Address a -> PaymentCredential a
paymentCredential (Address (_, (pc, _))) = pc

stakingCredential :: Address a -> StakingCredential a
stakingCredential (Address (_, (_, sc))) = sc