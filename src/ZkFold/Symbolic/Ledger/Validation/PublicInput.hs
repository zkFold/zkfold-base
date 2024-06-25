module ZkFold.Symbolic.Ledger.Validation.PublicInput where

import           Prelude                      hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Data.Bool    (Bool)
import           ZkFold.Symbolic.Ledger.Types (Input, LedgerState)

type PublicInputWitness a = a

publicInputIsValid ::
       LedgerState a
    -> Input a
    -> PublicInputWitness a
    -> Bool a
publicInputIsValid _ _ = undefined