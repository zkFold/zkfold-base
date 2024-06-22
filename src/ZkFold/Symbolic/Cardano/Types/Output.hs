{-# LANGUAGE DerivingVia #-}
module ZkFold.Symbolic.Cardano.Types.Output where

import           Prelude                               hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Symbolic.Cardano.Types.Address (Address)
import           ZkFold.Symbolic.Cardano.Types.Value   (Value)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool             (Bool)
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Eq               (Eq)
import           ZkFold.Symbolic.Data.Eq.Structural

type DatumHash a = ByteString 256 a

newtype Output tokens datum a = Output (Address a, (Value tokens a, DatumHash a))

deriving instance (Arithmetic a, KnownNat tokens) => SymbolicData a (Output tokens datum (ArithmeticCircuit a))

deriving via (Structural (Output tokens datum (ArithmeticCircuit a)))
         instance (Arithmetic a, KnownNat tokens) =>
         Eq (Bool (ArithmeticCircuit a)) (Output tokens datum (ArithmeticCircuit a))

txoAddress :: Output tokens datum a -> Address a
txoAddress (Output (addr, _)) = addr

txoTokens :: Output tokens datum a -> Value tokens a
txoTokens (Output (_, (v, _))) = v

txoDatumHash :: Output tokens datum a -> DatumHash a
txoDatumHash (Output (_, (_, dh))) = dh
