{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters
{-# LANGUAGE AllowAmbiguousTypes  #-}

module ZkFold.Symbolic.Cardano.Types.OutputRef where

import           GHC.Generics                        (Generic)
import           Prelude                             hiding (Bool, Eq, length, splitAt, (*), (+))
import qualified Prelude                             as Haskell

import           ZkFold.Symbolic.Cardano.Types.Basic
import           ZkFold.Symbolic.Class               (Symbolic (..))
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Combinators    (KnownRegisters, RegisterSize (..))
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.Input          (SymbolicInput)

type TxRefId context = ByteString 256 context
type TxRefIndex context = UInt 32 Auto context

data OutputRef context = OutputRef {
        outputRefId    :: TxRefId context,
        outputRefIndex :: TxRefIndex context
    }
    deriving (Generic)

deriving instance
    ( Haskell.Eq (TxRefId context)
    , Haskell.Eq (TxRefIndex context)
    ) => Haskell.Eq (OutputRef context)

instance (Symbolic context, KnownRegisters context 32 Auto)
    => SymbolicData (OutputRef context)

instance (Symbolic context, KnownRegisters context 32 Auto)
    => SymbolicInput (OutputRef context) where

instance (Symbolic context, KnownRegisters context 32 Auto)
    => Conditional (Bool context) (OutputRef context) where

instance (Symbolic context, KnownRegisters context 32 Auto)
    => Eq (OutputRef context) where
