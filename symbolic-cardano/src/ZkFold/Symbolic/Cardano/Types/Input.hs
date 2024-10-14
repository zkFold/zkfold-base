{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module ZkFold.Symbolic.Cardano.Types.Input where

import           Prelude                                 hiding (Bool, Eq, length, splitAt, (*), (+))
import qualified Prelude                                 as Haskell

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Symbolic.Cardano.Types.Address   (Address)
import           ZkFold.Symbolic.Cardano.Types.Output    (DatumHash, Output, txoAddress, txoDatumHash, txoTokens)
import           ZkFold.Symbolic.Cardano.Types.OutputRef (OutputRef)
import           ZkFold.Symbolic.Cardano.Types.Value     (Value)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Class

data Input tokens datum context = Input  {
        txiOutputRef :: OutputRef context,
        txiOutput    :: Output tokens datum context
    }

deriving instance
    ( Haskell.Eq (OutputRef context)
    , Haskell.Eq (Output tokens datum context)
    ) => Haskell.Eq (Input tokens datum context)

instance (Symbolic context, KnownNat tokens) => SymbolicData (Input tokens datum context) where
  type Context (Input tokens datum context) = Context (OutputRef context, Output tokens datum context)
  type Support (Input tokens datum context) = Support (OutputRef context, Output tokens datum context)
  type Layout (Input tokens datum context) = Layout (OutputRef context, Output tokens datum context)

  pieces (Input a b) = pieces (a, b)
  restore f = let (a, b) = restore f in Input a b

txiAddress :: Input tokens datum context -> Address context
txiAddress (Input _ txo) = txoAddress txo

txiTokens :: Input tokens datum context -> Value tokens context
txiTokens (Input _ txo) = txoTokens txo

txiDatumHash :: Input tokens datum context -> DatumHash context
txiDatumHash (Input _ txo) = txoDatumHash txo
