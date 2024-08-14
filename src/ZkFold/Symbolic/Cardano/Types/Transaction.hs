{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Cardano.Types.Transaction where

import           Prelude                                 hiding (Bool, Eq, length, splitAt, (*), (+))
import qualified Prelude                                 as Haskell

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Cardano.Types.Basic
import           ZkFold.Symbolic.Cardano.Types.Input     (Input)
import           ZkFold.Symbolic.Cardano.Types.Output    (Output)
import           ZkFold.Symbolic.Cardano.Types.OutputRef (OutputRef)
import           ZkFold.Symbolic.Cardano.Types.Value     (SingleAsset, Value)
import           ZkFold.Symbolic.Class                   (Symbolic)
import           ZkFold.Symbolic.Data.Class

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
    ( Symbolic context
    , KnownNat tokens
    , KnownNat rinputs
    , KnownNat inputs
    , KnownNat outputs
    , KnownNat mint
    , KnownNat (TypeSize context (SingleAsset context))
    , KnownNat (TypeSize context (UTCTime context))
    , KnownNat (TypeSize context (OutputRef context))
    , KnownNat (TypeSize context (Value tokens context))
    , KnownNat (TypeSize context (Output tokens datum context))
    , KnownNat (TypeSize context (Vector outputs (Output tokens datum context)))
    , KnownNat (TypeSize context (Input tokens datum context))
    , KnownNat (TypeSize context (Vector inputs (Input tokens datum context)))
    , KnownNat (TypeSize context (Vector rinputs (Input tokens datum context)))
    , KnownNat (TypeSize context (Value mint context))
    ) => SymbolicData context (Transaction inputs rinputs outputs tokens mint datum context)

txRefInputs :: Transaction inputs rinputs outputs tokens mint datum context -> Vector rinputs (Input tokens datum context)
txRefInputs (Transaction (ris, _)) = ris

txInputs :: Transaction inputs rinputs outputs tokens mint datum context -> Vector inputs (Input tokens datum context)
txInputs (Transaction (_, (is, _))) = is

txOutputs :: Transaction inputs rinputs outputs tokens mint datum context -> Vector outputs (Output tokens datum context)
txOutputs (Transaction (_, (_, (os, _)))) = os

txMint :: Transaction inputs rinputs outputs tokens mint datum context -> Value mint context
txMint (Transaction (_, (_, (_, (mint, _))))) = mint
