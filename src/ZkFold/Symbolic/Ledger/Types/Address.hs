module ZkFold.Symbolic.Ledger.Types.Address where

import           Prelude                               hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Contract (Contract, ContractId)

data Datum context

type SpendingPolicy tx w context = Contract tx (Datum context) w context

type Address context = ContractId context