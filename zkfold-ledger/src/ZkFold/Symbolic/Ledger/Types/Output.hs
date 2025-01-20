{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Ledger.Types.Output where

import           GHC.Generics                         (Generic)
import           Prelude                              hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Class                (Symbolic)
import           ZkFold.Symbolic.Data.Bool            (Bool)
import           ZkFold.Symbolic.Data.Class           (SymbolicData)
import           ZkFold.Symbolic.Data.Combinators     (KnownRegisters, RegisterSize (Auto))
import           ZkFold.Symbolic.Data.Conditional     (Conditional)
import           ZkFold.Symbolic.Data.Eq              (Eq)
import           ZkFold.Symbolic.Ledger.Types.Address (Address, Datum)
import           ZkFold.Symbolic.Ledger.Types.Value   (Value)

-- | Transaction output.
data Output context = Output
        { txoAddress :: Address context
        -- ^ Address at which the value is locked
        , txoValue   :: Value context
        -- ^ Value locked by the output
        , txoDatum   :: Datum context
        -- ^ Datum associated with the output
        } deriving Generic

instance (Symbolic context, KnownRegisters context 64 Auto) => SymbolicData (Output context)
instance (Symbolic context, KnownRegisters context 64 Auto) => Conditional (Bool context) (Output context)
instance (Symbolic context, KnownRegisters context 64 Auto) => Eq (Output context)
