module ZkFold.Symbolic.Ledger.Validation.PublicInput where

import           Prelude                      hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types

data PublicInputWitness context

publicInputIsValid ::
       BlockId context
    -> Input context
    -> PublicInputWitness context
    -> Bool context
publicInputIsValid _ _ = undefined