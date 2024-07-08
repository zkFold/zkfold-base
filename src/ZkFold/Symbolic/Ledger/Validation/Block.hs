module ZkFold.Symbolic.Ledger.Validation.Block where

import           Prelude                      hiding (Bool, Eq, length, splitAt, (*), (+), (==))

import           ZkFold.Symbolic.Ledger.Types

data BlockWitness context

newBlockIsValid ::
       BlockId context
    -> Block context
    -> BlockWitness context
    -> Bool context
newBlockIsValid _ _ _ = undefined