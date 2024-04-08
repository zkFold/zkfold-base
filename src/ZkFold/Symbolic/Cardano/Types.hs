{-# LANGUAGE UndecidableInstances #-}
module ZkFold.Symbolic.Cardano.Types where

import           Prelude                        hiding ((*), (+), length, splitAt)

import           ZkFold.Symbolic.Data.UInt
import           ZkFold.Symbolic.Data.UTCTime
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Compiler

newtype Transaction inputs rinputs outputs tokens datum a = Transaction
    ( Vector rinputs (Input datum tokens a)
    , (Vector inputs (Input datum tokens a)
    , (Vector outputs (Output datum tokens a)
    , (UTCTime a, UTCTime a)
    ))) deriving Eq

deriving instance
    ( KnownNat inputs
    , KnownNat rinputs
    , KnownNat outputs
    , KnownNat tokens
    , Arithmetizable i a
    , Arithmetizable i (UInt 11 a)
    , Arithmetizable i (UInt 32 a)
    , Arithmetizable i (UInt 64 a)
    , Arithmetizable i (ByteString 4 a)
    , Arithmetizable i (ByteString 224 a)
    , Arithmetizable i (ByteString 256 a)
    ) => Arithmetizable i (Transaction inputs rinputs outputs tokens datum a)

txInputs :: Transaction inputs rinputs outputs tokens datum a -> Vector inputs (Input datum tokens a)
txInputs (Transaction (_, (is, _))) = is

txOutputs :: Transaction inputs rinputs outputs tokens datum a -> Vector outputs (Output datum tokens a)
txOutputs (Transaction (_, (_, (os, _)))) = os

newtype TxId a = TxId a
    deriving (Eq, Arithmetizable i)

newtype Value n a = Value (Vector n (ByteString 224 a, (ByteString 256 a, UInt 64 a)))
    deriving Eq

deriving instance
    ( KnownNat n
    , Arithmetizable i a
    , Arithmetizable i (UInt 64 a)
    , Arithmetizable i (ByteString 224 a)
    , Arithmetizable i (ByteString 256 a)
    ) => Arithmetizable i (Value n a)

newtype Input datum tokens a = Input (OutputRef a, Output datum tokens a)
    deriving Eq

txiDatumHash :: Input tokens datum a -> ByteString 256 a
txiDatumHash (Input (_, txo))= txoDatumHash txo

deriving instance
    ( KnownNat tokens
    , Arithmetizable i a
    , Arithmetizable i (UInt 32 a)
    , Arithmetizable i (UInt 64 a)
    , Arithmetizable i (ByteString 4 a)
    , Arithmetizable i (ByteString 224 a)
    , Arithmetizable i (ByteString 256 a)
    ) => Arithmetizable i (Input datum tokens a)

newtype Output datum tokens a = Output (Address a, (Value tokens a, ByteString 256 a))
    deriving Eq

txoDatumHash :: Output datum tokens a -> ByteString 256 a
txoDatumHash (Output (_, (_, dh))) = dh

deriving instance
    ( KnownNat tokens
    , Arithmetizable i a
    , Arithmetizable i (UInt 64 a)
    , Arithmetizable i (ByteString 4 a)
    , Arithmetizable i (ByteString 224 a)
    , Arithmetizable i (ByteString 256 a)
    ) => Arithmetizable i (Output datum tokens a)

newtype OutputRef a = OutputRef (TxId a, UInt 32 a)
    deriving Eq

deriving instance
    (Arithmetizable i a, Arithmetizable i (UInt 32 a))
    => Arithmetizable i (OutputRef a)

newtype Address a = Address (ByteString 4 a, (ByteString 224 a, ByteString 224 a))
    deriving Eq

deriving instance
    ( Arithmetizable i (ByteString 4 a)
    , Arithmetizable i (ByteString 224 a)
    ) => Arithmetizable i (Address a)

newtype DatumHash datum a = DatumHash a
    deriving (Eq, Arithmetizable i)

newtype ScriptHash a = ScriptHash a
    deriving (Eq, Arithmetizable i)
