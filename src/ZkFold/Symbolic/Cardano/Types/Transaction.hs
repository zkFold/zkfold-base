{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Cardano.Types.Transaction where

import           Prelude                              hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Cardano.Types.Basic
import           ZkFold.Symbolic.Cardano.Types.Input  (Input)
import           ZkFold.Symbolic.Cardano.Types.Output (Output)
import           ZkFold.Symbolic.Cardano.Types.Value  (Value)
import           ZkFold.Symbolic.Compiler
import qualified ZkFold.Symbolic.Data.FieldElement    as FE
import           ZkFold.Symbolic.Data.UTCTime

newtype Transaction inputs rinputs outputs tokens mint datum context = Transaction
    ( Vector rinputs (Input tokens datum context)
    , (Vector inputs (Input tokens datum context)
    , (Vector outputs (Output tokens datum context)
    , (Value mint context
    , (UTCTime context F, UTCTime context F)
    ))))

-- TODO: Think how to prettify this abomination
deriving instance
    ( KnownNat (FE.TypeSize F CtxEvaluation (Value tokens CtxEvaluation))
    , KnownNat (FE.TypeSize F CtxEvaluation (Output tokens datum CtxEvaluation))
    , KnownNat (FE.TypeSize F CtxEvaluation (Vector outputs (Output tokens datum CtxEvaluation)))
    , KnownNat (FE.TypeSize F CtxEvaluation (Input tokens datum CtxEvaluation))
    , KnownNat (FE.TypeSize F CtxEvaluation (Vector inputs (Input tokens datum CtxEvaluation)))
    , KnownNat (FE.TypeSize F CtxEvaluation (Vector rinputs (Input tokens datum CtxEvaluation)))
    , KnownNat (FE.TypeSize F CtxEvaluation (Value mint CtxEvaluation))
    ) => FE.FieldElementData F Vector (Transaction inputs rinputs outputs tokens mint datum CtxEvaluation)

-- TODO: Think how to prettify this abomination
deriving instance
    ( KnownNat (TypeSize F (Value tokens CtxCompilation))
    , KnownNat (TypeSize F (Output tokens datum CtxCompilation))
    , KnownNat (TypeSize F (Vector outputs (Output tokens datum CtxCompilation)))
    , KnownNat (TypeSize F (Input tokens datum CtxCompilation))
    , KnownNat (TypeSize F (Vector inputs (Input tokens datum CtxCompilation)))
    , KnownNat (TypeSize F (Vector rinputs (Input tokens datum CtxCompilation)))
    , KnownNat (TypeSize F (Value mint CtxCompilation))
    ) => SymbolicData F (Transaction inputs rinputs outputs tokens mint datum CtxCompilation)

txRefInputs :: Transaction inputs rinputs outputs tokens mint datum context -> Vector rinputs (Input tokens datum context)
txRefInputs (Transaction (ris, _)) = ris

txInputs :: Transaction inputs rinputs outputs tokens mint datum context -> Vector inputs (Input tokens datum context)
txInputs (Transaction (_, (is, _))) = is

txOutputs :: Transaction inputs rinputs outputs tokens mint datum context -> Vector outputs (Output tokens datum context)
txOutputs (Transaction (_, (_, (os, _)))) = os

txMint :: Transaction inputs rinputs outputs tokens mint datum context -> Value mint context
txMint (Transaction (_, (_, (_, (mint, _))))) = mint
