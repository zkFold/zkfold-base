module ZkFold.Symbolic.Cardano.Types.Input where

import           Prelude                                 hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Symbolic.Cardano.Types.Address   (Address)
import           ZkFold.Symbolic.Cardano.Types.Output    (Output, DatumHash, txoAddress, txoTokens, txoDatumHash)
import           ZkFold.Symbolic.Cardano.Types.OutputRef (OutputRef)
import           ZkFold.Symbolic.Cardano.Types.Value     (Value)
import           ZkFold.Symbolic.Compiler

newtype Input tokens datum a = Input (OutputRef a, Output tokens datum a)

deriving instance (Arithmetic a, KnownNat tokens) => SymbolicData a (Input tokens datum (ArithmeticCircuit a))

txiOutputRef :: Input tokens datum a -> OutputRef a
txiOutputRef (Input (ref, _)) = ref

txiOutput :: Input tokens datum a -> Output tokens datum a
txiOutput (Input (_, txo)) = txo

txiAddress :: Input tokens datum a -> Address a
txiAddress (Input (_, txo)) = txoAddress txo

txiTokens :: Input tokens datum a -> Value tokens a
txiTokens (Input (_, txo)) = txoTokens txo

txiDatumHash :: Input tokens datum a -> DatumHash a
txiDatumHash (Input (_, txo)) = txoDatumHash txo