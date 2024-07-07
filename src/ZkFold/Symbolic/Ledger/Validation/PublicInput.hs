module ZkFold.Symbolic.Ledger.Validation.PublicInput where

import           Prelude                      hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Data.Bool    (Bool)
import           ZkFold.Symbolic.Ledger.Types

type PublicInputWitness a = a

publicInputIsValid ::
       BlockId a
    -> Input uint a
    -> PublicInputWitness a
    -> Bool a
publicInputIsValid _ _ = undefined