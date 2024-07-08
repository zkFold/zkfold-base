module ZkFold.Symbolic.Ledger.Validation.PublicInput where

import           Prelude                      hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types

-- | Witness data that is required to prove the validity of a public transaction input.
data PublicInputWitness context

-- | Checks if the public input is valid.
publicInputIsValid ::
       BlockId context
    -> Input context
    -> PublicInputWitness context
    -> Bool context
publicInputIsValid _ _ = undefined