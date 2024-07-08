module ZkFold.Symbolic.Ledger.Validation.PublicInput where

import           Prelude                      hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types

-- | Witness data that is required to prove the validity of a public transaction input.
data PublicInputWitness context

-- | Checks if the public input is valid.
publicInputIsValid ::
       BlockId context
    -- ^ The id of the current block.
    -> Input context
    -- ^ The transaction input to check.
    -> PublicInputWitness context
    -- ^ The witness data for the public input.
    -> Bool context
publicInputIsValid _ _ = undefined
