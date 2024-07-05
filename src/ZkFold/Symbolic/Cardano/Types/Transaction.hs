{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module ZkFold.Symbolic.Cardano.Types.Transaction where

import           Prelude                              hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Cardano.Types.Input  (Input)
import           ZkFold.Symbolic.Cardano.Types.Output (Output)
import           ZkFold.Symbolic.Cardano.Types.Value  (Value)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Combinators
import qualified ZkFold.Symbolic.Data.FieldElement    as FE
import           ZkFold.Symbolic.Data.UInt
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
    , KnownNat (FE.TypeSize a Vector (UTCTime Vector a))
    , KnownNat (FE.TypeSize a Vector (Value tokens Vector a))
    , KnownNat (FE.TypeSize a Vector (Output tokens datum Vector a))
    , KnownNat (FE.TypeSize a Vector (Vector outputs (Output tokens datum Vector a)))
    , KnownNat (FE.TypeSize a Vector (Input tokens datum Vector a))
    , KnownNat (FE.TypeSize a Vector (Vector inputs (Input tokens datum Vector a)))
    , KnownNat (FE.TypeSize a Vector (Vector rinputs (Input tokens datum Vector a)))
    , KnownNat (256 + NumberOfRegisters a 32)
    , KnownNat (FE.TypeSize a Vector (ByteString 224 Vector a, (ByteString 256 Vector a, UInt 64 Vector a)))
    ) => FE.FieldElementData a Vector (Transaction inputs rinputs outputs tokens datum Vector a)

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
    , KnownNat (TypeSize a (SingleAsset ArithmeticCircuit a))
    , KnownNat (256 + NumberOfRegisters a 32)
    ) => SymbolicData a (Transaction inputs rinputs outputs tokens datum ArithmeticCircuit a)

txRefInputs :: Transaction inputs rinputs outputs tokens datum b a -> Vector rinputs (Input tokens datum b a)
txRefInputs (Transaction (ris, _)) = ris

txInputs :: Transaction inputs rinputs outputs tokens datum b a -> Vector inputs (Input tokens datum b a)
txInputs (Transaction (_, (is, _))) = is

txOutputs :: Transaction inputs rinputs outputs tokens datum b a -> Vector outputs (Output tokens datum b a)
txOutputs (Transaction (_, (_, (os, _)))) = os

txMint :: Transaction inputs rinputs outputs tokens datum b a -> Value 1 b a
txMint (Transaction (_, (_, (_, (mint, _))))) = mint
