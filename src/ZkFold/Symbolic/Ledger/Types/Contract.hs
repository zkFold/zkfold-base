module ZkFold.Symbolic.Ledger.Types.Contract where

import           Prelude                           hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Basic
import           ZkFold.Symbolic.Ledger.Types.Hash (Hash)

newtype Contract tx pub prv backend = Contract (tx -> pub -> prv -> Bool backend)

type ContractId backend = Hash backend

contractId :: Contract tx pub prv backend -> ContractId backend
contractId _ = undefined

type ContractState backend = Hash backend

data ContractData backend