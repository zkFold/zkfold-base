module ZkFold.Symbolic.Ledger.Types.Contract where

import           Prelude                            hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Basic
import           ZkFold.Symbolic.Ledger.Types.Hash  (Hash)

-- | A contract is a specification on a transaction.
-- A contract must be valid if the corresponding triggering condition holds for the transaction.
-- See definitions of `SpendingContract` and `MintingContract` for details.
newtype Contract tx pub prv context = Contract (tx -> pub -> prv -> Bool context)

type ContractId context = Hash context

contractId :: Contract tx pub prv context -> ContractId context
contractId _ = undefined

-- | The "state" of a contract. Every contract verification invokes a transition to the new state.
type ContractState context = Hash context

-- | The public data that consumers need to construct transactions that satisfy the contract.
data ContractData context