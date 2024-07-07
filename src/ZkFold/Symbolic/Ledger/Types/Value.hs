module ZkFold.Symbolic.Ledger.Types.Value where

import           Prelude                               hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Basic
import           ZkFold.Symbolic.Ledger.Types.Contract (Contract, ContractId)

data Token backend

type MintingPolicy tx w backend = Contract tx (Token backend) w backend

data Value backend = Value (ContractId backend) (Token backend) (UInt64 backend)