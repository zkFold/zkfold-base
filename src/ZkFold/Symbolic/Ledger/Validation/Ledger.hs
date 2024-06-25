module ZkFold.Symbolic.Ledger.Validation.Ledger where

import           Prelude                      hiding (Bool, Eq, length, splitAt, (*), (+), (==))

import           ZkFold.Symbolic.Data.Bool    (Bool)
import           ZkFold.Symbolic.Ledger.Types (Transaction, LedgerState, LedgerUpdate)

type LedgerTransitionWitness a = a

ledgerTransitionIsValid ::
       LedgerState a
    -> Transaction a
    -> LedgerState a
    -> LedgerTransitionWitness a
    -> Bool a
ledgerTransitionIsValid _ _ _ _ = undefined

ledgerUpdate :: [Transaction a] -> LedgerUpdate a
ledgerUpdate _ = undefined