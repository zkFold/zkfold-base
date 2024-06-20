{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- Trust me bro

module ZkFold.Symbolic.Cardano.Types where

import           Prelude                            hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool          (Bool)
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Eq            (Eq)
import           ZkFold.Symbolic.Data.Eq.Structural
import           ZkFold.Symbolic.Data.UInt
import           ZkFold.Symbolic.Data.UTCTime


newtype Transaction inputs rinputs outputs tokens datum b a = Transaction
    ( Vector rinputs (Input tokens datum b a)
    , (Vector inputs (Input tokens datum b a)
    , (Vector outputs (Output tokens datum b a)
    , (UTCTime b a, UTCTime b a)
    )))

-- TODO: Think how to prettify this abomination
deriving instance
    ( Arithmetic a
    , KnownNat (TypeSize a (UTCTime ArithmeticCircuit a))
    , KnownNat (TypeSize a (Value tokens ArithmeticCircuit a))
    , KnownNat (TypeSize a (Output tokens datum ArithmeticCircuit a))
    , KnownNat (TypeSize a (Vector outputs (Output tokens datum ArithmeticCircuit a)))
    , KnownNat (TypeSize a (Input tokens datum ArithmeticCircuit a))
    , KnownNat (TypeSize a (Vector inputs (Input tokens datum ArithmeticCircuit a)))
    , KnownNat (TypeSize a (Vector rinputs (Input tokens datum ArithmeticCircuit a)))
    , KnownNat (1 + NumberOfRegisters a 32)
    , KnownNat (TypeSize a (ByteString 224 ArithmeticCircuit a, (ByteString 256 ArithmeticCircuit a, UInt 64 ArithmeticCircuit a)))
    ) => SymbolicData a (Transaction inputs rinputs outputs tokens datum ArithmeticCircuit a)

txInputs :: Transaction inputs rinputs outputs tokens datum b a -> Vector inputs (Input tokens datum b a)
txInputs (Transaction (_, (is, _))) = is

txOutputs :: Transaction inputs rinputs outputs tokens datum b a -> Vector outputs (Output tokens datum b a)
txOutputs (Transaction (_, (_, (os, _)))) = os


newtype TxId b a = TxId (b 1 a)

deriving instance Arithmetic a => SymbolicData a (TxId ArithmeticCircuit a)

newtype Value n b a = Value (Vector n (ByteString 224 b a, (ByteString 256 b a, UInt 64 b a)))

deriving instance
    ( Arithmetic a
    , KnownNat (TypeSize a (ByteString 224 ArithmeticCircuit a, (ByteString 256 ArithmeticCircuit a, UInt 64 ArithmeticCircuit a)))
    ) => SymbolicData a (Value n ArithmeticCircuit a)


newtype Input tokens datum b a = Input (OutputRef b a, Output tokens datum b a)

txiOutput :: Input tokens datum b a -> Output tokens datum b a
txiOutput (Input (_, txo)) = txo

txiDatumHash :: Input tokens datum b a -> ByteString 256 b a
txiDatumHash (Input (_, txo))= txoDatumHash txo

deriving instance
    ( Arithmetic a
    , KnownNat (TypeSize a (Value tokens ArithmeticCircuit a))
    , KnownNat (1 + NumberOfRegisters a 32)
    , KnownNat (TypeSize a (ByteString 224 ArithmeticCircuit a, (ByteString 256 ArithmeticCircuit a, UInt 64 ArithmeticCircuit a)))
    ) => SymbolicData a (Input tokens datum ArithmeticCircuit a)

newtype Output tokens datum b a = Output (Address b a, (Value tokens b a, ByteString 256 b a))

txoAddress :: Output tokens datum b a -> Address b a
txoAddress (Output (addr, _)) = addr

txoDatumHash :: Output tokens datum b a -> ByteString 256 b a
txoDatumHash (Output (_, (_, dh))) = dh

txoTokens :: Output tokens datum b a -> Value tokens b a
txoTokens (Output (_, (v, _))) = v

deriving instance
    ( Arithmetic a
    , KnownNat (TypeSize a (Value tokens ArithmeticCircuit a))
    , KnownNat (TypeSize a (ByteString 224 ArithmeticCircuit a, (ByteString 256 ArithmeticCircuit a, UInt 64 ArithmeticCircuit a)))
    ) => SymbolicData a (Output tokens datum ArithmeticCircuit a)

deriving via (Structural (Output tokens datum ArithmeticCircuit a))
         instance
            ( Arithmetic a
            , ts ~ TypeSize a (Output tokens datum ArithmeticCircuit a)
            , 1 <= ts
            , KnownNat ts
            , KnownNat (TypeSize a (Value tokens ArithmeticCircuit a))
            , KnownNat (TypeSize a (ByteString 224 ArithmeticCircuit a, (ByteString 256 ArithmeticCircuit a, UInt 64 ArithmeticCircuit a)))
            ) => Eq (Bool (ArithmeticCircuit 1 a)) (Output tokens datum ArithmeticCircuit a)

newtype OutputRef b a = OutputRef (TxId b a, UInt 32 b a)

deriving instance Arithmetic a => SymbolicData a (OutputRef ArithmeticCircuit a)

newtype Address b a = Address (ByteString 4 b a, (ByteString 224 b a, ByteString 224 b a))

deriving instance Arithmetic a => SymbolicData a (Address ArithmeticCircuit a)

deriving via (Structural (Address ArithmeticCircuit a))
         instance Arithmetic a =>
         Eq (Bool (ArithmeticCircuit 1 a)) (Address ArithmeticCircuit a)

paymentCredential :: Address b a -> ByteString 224 b a
paymentCredential (Address (_, (pc, _))) = pc

newtype DatumHash datum b a = DatumHash (b 1 a)
    deriving (SymbolicData i)

newtype ScriptHash b a = ScriptHash (b 1 a)
    deriving (SymbolicData i)
