module ZkFold.Symbolic.Ledger.Validation.Contract where

import           Prelude                      hiding (Bool, Eq, length, splitAt, (*), (+), (==))

import           ZkFold.Symbolic.Ledger.Types

-- | Witness data for a spending contract.
data SpendingContractWitness context

-- | Witness data for a minting contract.
data MintingContractWitness context

-- | Checks if a contract is satisfied.
spendingContractIsSatisfied ::
       Transaction context
    -> ContractId context
    -> Datum context
    -> SpendingContractWitness context
    -> Bool context
spendingContractIsSatisfied _ _ = undefined

-- | Checks if a minting contract is satisfied.
mintingContractIsSatisfied ::
       Transaction context
    -> ContractId context
    -> Token context
    -> MintingContractWitness context
    -> Bool context
mintingContractIsSatisfied _ _ = undefined