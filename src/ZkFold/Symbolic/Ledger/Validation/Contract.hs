module ZkFold.Symbolic.Ledger.Validation.Contract where

import           Prelude                      hiding (Bool, Eq, length, splitAt, (*), (+), (==))

import           ZkFold.Symbolic.Ledger.Types

contractStateTransition ::
    Hashable context (ContractState context, TransactionId context)
    => ContractState context
    -> TransactionId context
    -> ContractState context
contractStateTransition s i = hash (s, i)