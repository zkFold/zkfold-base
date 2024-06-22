module ZkFold.Symbolic.Cardano.Types.Input where

import           Prelude                                 hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Symbolic.Cardano.Types.Output    (Output, txoDatumHash)
import           ZkFold.Symbolic.Cardano.Types.OutputRef (OutputRef)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.ByteString

newtype Input tokens datum a = Input (OutputRef a, Output tokens datum a)

deriving instance (Arithmetic a, KnownNat tokens) => SymbolicData a (Input tokens datum (ArithmeticCircuit a))

txiOutput :: Input tokens datum a -> Output tokens datum a
txiOutput (Input (_, txo)) = txo

txiDatumHash :: Input tokens datum a -> ByteString 256 a
txiDatumHash (Input (_, txo))= txoDatumHash txo