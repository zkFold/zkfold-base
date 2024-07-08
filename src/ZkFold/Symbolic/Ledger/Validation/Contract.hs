module ZkFold.Symbolic.Ledger.Validation.Contract where

import           Prelude                      hiding (Bool, Eq, length, splitAt, (*), (+), (==))

import           ZkFold.Symbolic.Ledger.Types

-- A contract state transition happens when a transaction must satisfy the contract.
contractStateTransition ::
    Hashable context (ContractState context, TransactionId context)
    => ContractState context
    -> TransactionId context
    -> ContractState context
contractStateTransition s i = hash (s, i)