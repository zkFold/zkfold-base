{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters
{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Symbolic.Cardano.Types.OutputRef where

import           Prelude                             hiding (Bool, Eq, length, splitAt, (*), (+))
import qualified Prelude                             as Haskell

import           ZkFold.Base.Control.HApplicative    (HApplicative)
import           ZkFold.Symbolic.Cardano.Types.Basic
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators    (RegisterSize (..), NumberOfRegisters)
import ZkFold.Symbolic.Data.Input (SymbolicInput, isValid)
import ZkFold.Symbolic.Class (Symbolic (..))
import GHC.TypeNats (KnownNat)

type TxRefId context = ByteString 256 context
type TxRefIndex context = UInt 32 Auto context

data OutputRef context = OutputRef {
        outputRefId    :: TxRefId context,
        outputRefIndex :: TxRefIndex context
    }

deriving instance
    ( Haskell.Eq (TxRefId context)
    , Haskell.Eq (TxRefIndex context)
    ) => Haskell.Eq (OutputRef context)

instance HApplicative context => SymbolicData (OutputRef context) where
  type Context (OutputRef context) = Context (TxRefId context, TxRefIndex context)
  type Support (OutputRef context) = Support (TxRefId context, TxRefIndex context)
  type Layout (OutputRef context) = Layout (TxRefId context, TxRefIndex context)

  pieces (OutputRef a b) = pieces (a, b)
  restore f = let (a, b) = restore f in OutputRef a b

instance 
    ( HApplicative context
    , Symbolic context
    , KnownNat (NumberOfRegisters (BaseField context) 32 Auto)
    ) => SymbolicInput (OutputRef context) where
    isValid (OutputRef orId orInd) = isValid (orId, orInd)
