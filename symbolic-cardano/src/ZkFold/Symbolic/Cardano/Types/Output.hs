{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Cardano.Types.Output (
    module ZkFold.Symbolic.Cardano.Types.Output.Datum,
    Output(..),
    Liability(..)
) where

import           GHC.Generics                               (Generic)
import           Prelude                                    hiding (Bool, Eq, length, splitAt, (*), (+))
import qualified Prelude                                    as Haskell

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Symbolic.Cardano.Types.Address      (Address)
import           ZkFold.Symbolic.Cardano.Types.Basic
import           ZkFold.Symbolic.Cardano.Types.Output.Datum
import           ZkFold.Symbolic.Cardano.Types.Value        (SingleAsset, Value)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Conditional           (Conditional)
import           ZkFold.Symbolic.Data.Eq                    (Eq)
import           ZkFold.Symbolic.Data.Input                 (SymbolicInput (..))

data Liability context
    = Liability
        { lLiability :: SingleAsset context -- Liability in native tokens
        , lBabel     :: SingleAsset context -- Offer in any other tokens
        }

deriving instance Generic (Liability context)
deriving instance (Haskell.Eq (SingleAsset context)) => Haskell.Eq (Liability context)
deriving instance (Symbolic context) => SymbolicData (Liability context)
deriving instance (Symbolic context) => SymbolicInput (Liability context)

data Output tokens datum context = Output {
        txoAddress   :: Address context,
        txoTokens    :: Value tokens context,
        txoDatumHash :: DatumHash context
    }

deriving instance
    ( Haskell.Eq (Address context)
    , Haskell.Eq (Value tokens context)
    , Haskell.Eq (DatumHash context)
    ) => Haskell.Eq (Output tokens datum context)

deriving instance Generic (Output tokens datum context)
deriving instance (KnownNat tokens, Symbolic context) => SymbolicData (Output tokens datum context)
deriving instance (Symbolic context, KnownNat tokens) => SymbolicInput (Output tokens datum context)
deriving instance (Symbolic context, KnownNat tokens) => Conditional (Bool context) (Output tokens datum context)
deriving instance (Symbolic context, KnownNat tokens) => Eq (Bool context) (Output tokens datum context)
