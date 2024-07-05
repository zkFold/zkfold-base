{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Cardano.Types.Address where

import           Prelude                            hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Base.Data.Vector            (Vector)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool          (Bool)
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Eq            (Eq)
import           ZkFold.Symbolic.Data.Eq.Structural
import           ZkFold.Symbolic.Data.FieldElement  (FieldElementData)

type AddressType b a = ByteString 4 b a
type PaymentCredential b a = ByteString 224 b a
type StakingCredential b a = ByteString 224 b a

newtype Address b a = Address (AddressType b a, (PaymentCredential b a, StakingCredential b a))

deriving instance Arithmetic a => FieldElementData a Vector (Address Vector a)

deriving instance Arithmetic a => SymbolicData a (Address ArithmeticCircuit a)

deriving via (Structural (Address ArithmeticCircuit a))
         instance Arithmetic a =>
         Eq (Bool (ArithmeticCircuit 1 a)) (Address ArithmeticCircuit a)

addressType :: Address b a -> AddressType b a
addressType (Address (t, _)) = t

paymentCredential :: Address b a -> PaymentCredential b a
paymentCredential (Address (_, (pc, _))) = pc

stakingCredential :: Address b a -> StakingCredential b a
stakingCredential (Address (_, (_, sc))) = sc
