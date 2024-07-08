module ZkFold.Symbolic.Ledger.Validation.Block where

import           Prelude                      hiding (Bool, Eq, length, splitAt, (*), (+), (==))

import           ZkFold.Symbolic.Ledger.Types

-- | Witness data that is required to prove the validity of a block.
data BlockWitness context

-- | Checks if the new block is valid.
newBlockIsValid ::
       BlockId context
    -> Block context
    -> BlockWitness context
    -> Bool context
newBlockIsValid _ _ _ = undefined