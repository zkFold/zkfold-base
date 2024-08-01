{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Cardano.Types.Transaction where

import           Prelude                              hiding (Bool, Eq, length, splitAt, (*), (+))
import qualified Prelude                              as Haskell

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Cardano.Types.Basic
import           ZkFold.Symbolic.Cardano.Types.Input  (Input)
import           ZkFold.Symbolic.Cardano.Types.Output (Output)
import           ZkFold.Symbolic.Cardano.Types.Value  (Value)
import           ZkFold.Symbolic.Compiler
import qualified ZkFold.Symbolic.Data.FieldElement    as FE

newtype Transaction inputs rinputs outputs tokens mint datum context = Transaction
    ( Vector rinputs (Input tokens datum context)
    , (Vector inputs (Input tokens datum context)
    , (Vector outputs (Output tokens datum context)
    , (Value mint context
    , (UTCTime context, UTCTime context)
    ))))

deriving instance
    ( Haskell.Eq (Vector rinputs (Input tokens datum context))
    , Haskell.Eq (Vector inputs (Input tokens datum context))
    , Haskell.Eq (Vector outputs (Output tokens datum context))
    , Haskell.Eq (Value mint context)
    , Haskell.Eq (UTCTime context)
    ) => Haskell.Eq (Transaction inputs rinputs outputs tokens mint datum context)

-- TODO: Think how to prettify this abomination
deriving instance
    ( KnownNat (FE.TypeSize CtxEvaluation (Value tokens CtxEvaluation))
    , KnownNat (FE.TypeSize CtxEvaluation (Output tokens datum CtxEvaluation))
    , KnownNat (FE.TypeSize CtxEvaluation (Vector outputs (Output tokens datum CtxEvaluation)))
    , KnownNat (FE.TypeSize CtxEvaluation (Input tokens datum CtxEvaluation))
    , KnownNat (FE.TypeSize CtxEvaluation (Vector inputs (Input tokens datum CtxEvaluation)))
    , KnownNat (FE.TypeSize CtxEvaluation (Vector rinputs (Input tokens datum CtxEvaluation)))
    , KnownNat (FE.TypeSize CtxEvaluation (Value mint CtxEvaluation))
    ) => FE.FieldElementData CtxEvaluation (Transaction inputs rinputs outputs tokens mint datum CtxEvaluation)

-- TODO: Think how to prettify this abomination
deriving instance
    ( KnownNat tokens
    , KnownNat rinputs
    , KnownNat inputs
    , KnownNat outputs
    , KnownNat mint
    , KnownNat (TypeSize F (Value tokens CtxCompilation))
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
