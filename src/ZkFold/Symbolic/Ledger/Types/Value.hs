module ZkFold.Symbolic.Ledger.Types.Value where

import           Prelude                               hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Basic
import           ZkFold.Symbolic.Ledger.Types.Contract (Contract, ContractId)

data Token context

type MintingPolicy tx w context = Contract tx (Token context) w context

data Value context = Value (ContractId context) (Token context) (UInt64 context)