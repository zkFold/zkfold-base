module ZkFold.Symbolic.Ledger.Validation.Contract where

import           Prelude                      hiding (Bool, Eq, length, splitAt, (*), (+), (==))

import           ZkFold.Symbolic.Ledger.Types (ContractState, LedgerHash (..), TransactionId)

contractStateTransition ::
    (LedgerHash (ContractState a, TransactionId a) (ContractState a))
    => ContractState a
    -> TransactionId a
    -> ContractState a
contractStateTransition s i = ledgerHash (s, i)