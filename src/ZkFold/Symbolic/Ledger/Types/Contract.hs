module ZkFold.Symbolic.Ledger.Types.Contract where

import           Prelude                            hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Data.Bool          (Bool)

newtype Contract tx pub prv a = Contract (tx -> pub -> prv -> Bool a)

type ContractId a = a

type ContractState a = a

type ContractData a = [a]