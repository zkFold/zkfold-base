{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module ZkFold.Symbolic.Cardano.Types.Input where

import           Prelude                                 hiding (Bool, Eq, length, splitAt, (*), (+))
import qualified Prelude                                 as Haskell

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Symbolic.Cardano.Types.Address   (Address)
import           ZkFold.Symbolic.Cardano.Types.Output    (DatumHash, Output, txoAddress, txoDatumHash, txoTokens)
import           ZkFold.Symbolic.Cardano.Types.OutputRef (OutputRef)
import           ZkFold.Symbolic.Cardano.Types.Value     (Value, SingleAsset)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Class

newtype Input tokens datum context = Input (OutputRef context, Output tokens datum context)

deriving instance
    ( Haskell.Eq (OutputRef context)
    , Haskell.Eq (Output tokens datum context)
    ) => Haskell.Eq (Input tokens datum context)

deriving instance
    ( Symbolic context
    , KnownNat tokens
    , KnownNat (TypeSize context (OutputRef context))
    , KnownNat (TypeSize context (SingleAsset context))
    , KnownNat (TypeSize context (Value tokens context))
    ) => SymbolicData context (Input tokens datum context)

txiOutputRef :: Input tokens datum context -> OutputRef context
txiOutputRef (Input (ref, _)) = ref

txiOutput :: Input tokens datum context -> Output tokens datum context
txiOutput (Input (_, txo)) = txo

txiAddress :: Input tokens datum context -> Address context
txiAddress (Input (_, txo)) = txoAddress txo

txiTokens :: Input tokens datum context -> Value tokens context
txiTokens (Input (_, txo)) = txoTokens txo

txiDatumHash :: Input tokens datum context -> DatumHash context
txiDatumHash (Input (_, txo)) = txoDatumHash txo
