module ZkFold.Symbolic.Ledger.Types.Address where

import           Prelude                               hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Contract (Contract, ContractId)

data Datum a

type SpendingPolicy tx w a = Contract tx (Datum a) w a

type Address a = ContractId a