module ZkFold.Symbolic.Ledger.Validation.Contract where

import           Prelude                      hiding (Bool, Eq, length, splitAt, (*), (+), (==))

import           ZkFold.Symbolic.Ledger.Types

contractStateTransition ::
    Hashable backend (ContractState backend, TransactionId backend)
    => ContractState backend
    -> TransactionId backend
    -> ContractState backend
contractStateTransition s i = hash (s, i)