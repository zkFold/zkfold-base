module ZkFold.Symbolic.Cardano.Types.Transaction where

import           Prelude                              hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Cardano.Types.Input  (Input)
import           ZkFold.Symbolic.Cardano.Types.Output (Output)
import           ZkFold.Symbolic.Cardano.Types.Value  (Value)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.UTCTime

newtype Transaction inputs rinputs outputs tokens datum b a = Transaction
    ( Vector rinputs (Input tokens datum b a)
    , (Vector inputs (Input tokens datum b a)
    , (Vector outputs (Output tokens datum b a)
    , (Value 1 b a
    , (UTCTime b a, UTCTime b a)
    ))))

deriving instance
    ( Arithmetic a
    , KnownNat inputs
    , KnownNat rinputs
    , KnownNat outputs
    , KnownNat tokens
    ) => SymbolicData a (Transaction inputs rinputs outputs tokens datum ArithmeticCircuit a)

txRefInputs :: Transaction inputs rinputs outputs tokens datum b a -> Vector rinputs (Input tokens datum b a)
txRefInputs (Transaction (ris, _)) = ris

txInputs :: Transaction inputs rinputs outputs tokens datum b a -> Vector inputs (Input tokens datum b a)
txInputs (Transaction (_, (is, _))) = is

txOutputs :: Transaction inputs rinputs outputs tokens datum b a -> Vector outputs (Output tokens datum b a)
txOutputs (Transaction (_, (_, (os, _)))) = os

txMint :: Transaction inputs rinputs outputs tokens datum b a -> Value 1 b a
txMint (Transaction (_, (_, (_, (mint, _))))) = mint
