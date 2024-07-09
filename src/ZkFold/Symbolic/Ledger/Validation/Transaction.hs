module ZkFold.Symbolic.Ledger.Validation.Transaction where

import           Prelude                                    hiding (Bool, Eq, length, splitAt, (&&), (*), (+), (==), all)

import           ZkFold.Symbolic.Data.Bool                  (BoolType (..), all)
import           ZkFold.Symbolic.Ledger.Types
import           ZkFold.Symbolic.Ledger.Validation.Contract

-- | Witness data for the inputs of a transaction.
data TransactionInputsWitness context

-- | Witness data for a transaction satisfies the included contracts.
type TransactionContractsWitness context = [(ContractId context, ContractWitness context)]

-- | Witness data for a transaction.
type TransactionWitness context = (TransactionInputsWitness context, TransactionContractsWitness context)

-- | Checks if the inputs of a transaction are valid.
transactionInputsAreValid ::
       BlockId context
    -- ^ The id of the current block.
    -> Transaction context
    -- ^ The transaction to check.
    -> TransactionInputsWitness context
    -- ^ The witness data for the inputs of the transaction.
    -> Bool context
transactionInputsAreValid _ _ _ = undefined

-- | Checks if the balance of a transaction is correct.
transactionBalanceIsCorrect :: Transaction context -> Bool context
transactionBalanceIsCorrect _ = undefined

-- | Checks if a transaction satisfies the included contracts.
transactionContractsAreSatisfied ::
   BoolType (Bool context) =>
      Transaction context
   -> TransactionContractsWitness context
   -> Bool context
transactionContractsAreSatisfied _ ws =
   let
      -- TODO: check that we verify all included contracts
   in all (uncurry contractIsSatisfied) ws

-- | Checks if a transaction is valid.
transactionIsValid ::
       BoolType (Bool context)
    => BlockId context
    -- ^ The id of the current block.
    -> Transaction context
    -- ^ The transaction to check.
    -> TransactionWitness context
    -- ^ The witness data for the inputs of the transaction.
    -> Bool context
transactionIsValid s t (wInputs, wContracts) =
       transactionInputsAreValid s t wInputs
    && transactionBalanceIsCorrect t
    && transactionContractsAreSatisfied t wContracts
