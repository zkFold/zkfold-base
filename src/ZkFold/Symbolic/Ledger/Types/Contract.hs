module ZkFold.Symbolic.Ledger.Types.Contract where

import           Prelude                           hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Basic
import           ZkFold.Symbolic.Ledger.Types.Hash (Hash)

newtype Contract tx pub prv context = Contract (tx -> pub -> prv -> Bool context)

type ContractId context = Hash context

contractId :: Contract tx pub prv context -> ContractId context
contractId _ = undefined

type ContractState context = Hash context

data ContractData context