module ZkFold.Symbolic.Ledger.Types.Address where

import           Prelude                               hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Contract (Contract, ContractId)

data Datum backend

type SpendingPolicy tx w backend = Contract tx (Datum backend) w backend

type Address backend = ContractId backend