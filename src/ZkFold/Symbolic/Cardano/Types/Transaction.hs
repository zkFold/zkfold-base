module ZkFold.Symbolic.Cardano.Types.Transaction where

import           Prelude                              hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Cardano.Types.Input  (Input)
import           ZkFold.Symbolic.Cardano.Types.Output (Output)
import           ZkFold.Symbolic.Cardano.Types.Value  (Value)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.UTCTime

newtype Transaction inputs rinputs outputs tokens datum a = Transaction
    ( Vector rinputs (Input tokens datum a)
    , (Vector inputs (Input tokens datum a)
    , (Vector outputs (Output tokens datum a)
    , (Value 1 a
    , (UTCTime a, UTCTime a)
    ))))

deriving instance
    ( Arithmetic a
    , KnownNat inputs
    , KnownNat rinputs
    , KnownNat outputs
    , KnownNat tokens
    ) => SymbolicData a (Transaction inputs rinputs outputs tokens datum (ArithmeticCircuit a))

txRefInputs :: Transaction inputs rinputs outputs tokens datum a -> Vector rinputs (Input tokens datum a)
txRefInputs (Transaction (ris, _)) = ris

txInputs :: Transaction inputs rinputs outputs tokens datum a -> Vector inputs (Input tokens datum a)
txInputs (Transaction (_, (is, _))) = is

txOutputs :: Transaction inputs rinputs outputs tokens datum a -> Vector outputs (Output tokens datum a)
txOutputs (Transaction (_, (_, (os, _)))) = os

txMint :: Transaction inputs rinputs outputs tokens datum a -> Value 1 a
txMint (Transaction (_, (_, (_, (mint, _))))) = mint
