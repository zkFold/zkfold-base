module ZkFold.Symbolic.Ledger.Validation.Contract where

import           Prelude                      hiding (Bool, Eq, length, splitAt, (*), (+), (==))

import           ZkFold.Symbolic.Ledger.Types

-- | Witness data for a contract.
data ContractWitness context

-- | Checks if a contract is satisfied.
contractIsSatisfied ::
       Transaction context
    -> ContractId context
    -> ContractWitness context
    -> Bool context
contractIsSatisfied _ _ = undefined