module ZkFold.Symbolic.Ledger.Types.Contract where

import           Prelude                           hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Data.Bool         (Bool)
import           ZkFold.Symbolic.Ledger.Types.Hash (Hash)

newtype Contract tx pub prv a = Contract (tx -> pub -> prv -> Bool a)

type ContractId a = Hash a

contractId :: Contract tx pub prv a -> ContractId a
contractId _ = undefined

type ContractState a = Hash a

data ContractData a