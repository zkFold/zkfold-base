module ZkFold.Symbolic.Ledger.Validation.PublicInput where

import           Prelude                      hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types

data PublicInputWitness backend

publicInputIsValid ::
       BlockId backend
    -> Input backend
    -> PublicInputWitness backend
    -> Bool backend
publicInputIsValid _ _ = undefined