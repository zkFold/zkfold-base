module ZkFold.Symbolic.Ledger.Types.Value where

import           Prelude                               hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Contract (Contract, ContractId)

data Token a

type MintingPolicy tx w a = Contract tx (Token a) w a

data Value uint a = Value (ContractId a) (Token a) (uint a)