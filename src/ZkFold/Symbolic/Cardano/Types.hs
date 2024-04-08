{-# LANGUAGE UndecidableInstances #-}
module ZkFold.Symbolic.Cardano.Types where

import           Prelude                        hiding ((*), (+), length, splitAt)

import           ZkFold.Symbolic.Data.UInt
import           ZkFold.Symbolic.Data.UTCTime
import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Compiler

newtype Transaction inputs rinputs outputs tokens datum a = Transaction
    ( Vector rinputs (Input datum a)
    , (Vector inputs (Input datum a)
    , (Vector outputs (Output tokens a)
    , (UTCTime a, UTCTime a)
    ))) deriving Eq

deriving instance
    ( Finite inputs
    , Finite rinputs
    , Finite outputs
    , Finite tokens
    , Arithmetizable i a
    , Arithmetizable i (datum a)
    , Arithmetizable i (UInt 11 a)
    , Arithmetizable i (UInt 32 a)
    , Arithmetizable i (UInt 64 a)
    ) => Arithmetizable i (Transaction inputs rinputs outputs tokens datum a)

txInputs :: Transaction inputs rinputs outputs tokens datum a -> Vector inputs (Input datum a)
txInputs (Transaction (_, (is, _))) = is

newtype TxId a = TxId a
    deriving (Eq, Arithmetizable i)

newtype Value n a = Value (Vector n ({- Bytes a-} a, ({- Bytes a -} a, UInt 64 a)))
    deriving Eq

deriving instance
    (Finite n, Arithmetizable i a, Arithmetizable i (UInt 64 a))
    => Arithmetizable i (Value n a)

newtype Input datum a = Input (OutputRef a, (a, datum a))
    deriving Eq

txiDatum :: Input datum a -> datum a
txiDatum (Input (_, (_, datum))) = datum

deriving instance
    (Arithmetizable i a, Arithmetizable i (UInt 32 a), Arithmetizable i (datum a))
    => Arithmetizable i (Input datum a)

newtype Output tokens a = Output (Address a, (Value tokens a, a))
    deriving Eq

deriving instance
    (Finite tokens, Arithmetizable i a, Arithmetizable i (UInt 64 a))
    => Arithmetizable i (Output tokens a)

newtype OutputRef a = OutputRef (TxId a, UInt 32 a)
    deriving Eq

deriving instance
    (Arithmetizable i a, Arithmetizable i (UInt 32 a))
    => Arithmetizable i (OutputRef a)

newtype Address a = Address ({- Bytes a-} a, ({- Bytes a-} a, {- Bytes a-} a))
    deriving (Eq, Arithmetizable i)

newtype DatumHash datum a = DatumHash a
    deriving (Eq, Arithmetizable i)

newtype ScriptHash a = ScriptHash a
    deriving (Eq, Arithmetizable i)
