module ZkFold.Symbolic.Cardano.Types where

import           Prelude                          hiding (length, splitAt, (*), (+))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.UInt
import           ZkFold.Symbolic.Data.UTCTime

newtype Transaction inputs rinputs outputs tokens datum a = Transaction
    ( Vector rinputs (Input tokens datum a)
    , (Vector inputs (Input tokens datum a)
    , (Vector outputs (Output tokens datum a)
    , (UTCTime a, UTCTime a)
    ))) deriving Eq

deriving instance
    ( Arithmetic a
    , KnownNat inputs
    , KnownNat rinputs
    , KnownNat outputs
    , KnownNat tokens
    ) => SymbolicData a (Transaction inputs rinputs outputs tokens datum (ArithmeticCircuit a))

txInputs :: Transaction inputs rinputs outputs tokens datum a -> Vector inputs (Input tokens datum a)
txInputs (Transaction (_, (is, _))) = is

txOutputs :: Transaction inputs rinputs outputs tokens datum a -> Vector outputs (Output tokens datum a)
txOutputs (Transaction (_, (_, (os, _)))) = os

newtype TxId a = TxId a
    deriving Eq

deriving instance Arithmetic a => SymbolicData a (TxId (ArithmeticCircuit a))

newtype Value n a = Value (Vector n (ByteString 224 a, (ByteString 256 a, UInt 64 a)))
    deriving Eq

deriving instance (Arithmetic a, KnownNat n) => SymbolicData a (Value n (ArithmeticCircuit a))

newtype Input tokens datum a = Input (OutputRef a, Output tokens datum a)
    deriving Eq

txiOutput :: Input tokens datum a -> Output tokens datum a
txiOutput (Input (_, txo)) = txo

txiDatumHash :: Input tokens datum a -> ByteString 256 a
txiDatumHash (Input (_, txo))= txoDatumHash txo

deriving instance (Arithmetic a, KnownNat tokens) => SymbolicData a (Input tokens datum (ArithmeticCircuit a))

newtype Output tokens datum a = Output (Address a, (Value tokens a, ByteString 256 a))
    deriving Eq

txoAddress :: Output tokens datum a -> Address a
txoAddress (Output (addr, _)) = addr

txoDatumHash :: Output tokens datum a -> ByteString 256 a
txoDatumHash (Output (_, (_, dh))) = dh

deriving instance (Arithmetic a, KnownNat tokens) => SymbolicData a (Output tokens datum (ArithmeticCircuit a))

newtype OutputRef a = OutputRef (TxId a, UInt 32 a)
    deriving Eq

deriving instance Arithmetic a => SymbolicData a (OutputRef (ArithmeticCircuit a))

newtype Address a = Address (ByteString 4 a, (ByteString 224 a, ByteString 224 a))
    deriving Eq

paymentCredential :: Address a -> ByteString 224 a
paymentCredential (Address (_, (pc, _))) = pc

deriving instance Arithmetic a => SymbolicData a (Address (ArithmeticCircuit a))

newtype DatumHash datum a = DatumHash a
    deriving (Eq, SymbolicData i)

newtype ScriptHash a = ScriptHash a
    deriving (Eq, SymbolicData i)
