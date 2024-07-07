module ZkFold.Symbolic.Ledger.Validation.Contract where

import           Prelude                      hiding (Bool, Eq, length, splitAt, (*), (+), (==))

import           ZkFold.Symbolic.Ledger.Types

contractStateTransition ::
    Hashable a (ContractState a, TransactionId a)
    => ContractState a
    -> TransactionId a
    -> ContractState a
contractStateTransition s i = hash (s, i)