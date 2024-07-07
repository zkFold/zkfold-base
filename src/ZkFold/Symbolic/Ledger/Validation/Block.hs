module ZkFold.Symbolic.Ledger.Validation.Block where

import           Prelude                      hiding (Bool, Eq, length, splitAt, (*), (+), (==))

import           ZkFold.Symbolic.Data.Bool    (Bool)
import           ZkFold.Symbolic.Ledger.Types

type BlockWitness a = a

newBlockIsValid ::
       BlockId a
    -> Block uint utc a
    -> BlockWitness a
    -> Bool a
newBlockIsValid _ _ _ = undefined