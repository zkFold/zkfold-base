module ZkFold.Symbolic.Ledger.Validation.Block where

import           Prelude                      hiding (Bool, Eq, length, splitAt, (*), (+), (==))

import           ZkFold.Symbolic.Ledger.Types

data BlockWitness backend

newBlockIsValid ::
       BlockId backend
    -> Block backend
    -> BlockWitness backend
    -> Bool backend
newBlockIsValid _ _ _ = undefined