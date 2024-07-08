module ZkFold.Symbolic.Ledger.Validation.Transaction where

import           Prelude                         hiding (Bool, Eq, length, splitAt, (*), (+), (==), (&&))

import           ZkFold.Symbolic.Data.Bool       (BoolType (..))
import           ZkFold.Symbolic.Ledger.Types

-- | Witness data for the inputs of a transaction.
data TransactionInputsWitness context

-- | Checks if the inputs of a transaction are valid.
transactionInputsAreValid ::
       BlockId context
    -> Transaction context
    -> TransactionInputsWitness context
    -> Bool context
transactionInputsAreValid _ _ _ = undefined

-- | Checks if the balance of a transaction is correct.
transactionBalanceIsCorrect :: Transaction context -> Bool a
transactionBalanceIsCorrect _ = undefined

-- | Checks if the contracts of a transaction succeed.
transactionContractsSucceed :: Transaction context -> Bool a
transactionContractsSucceed _ = undefined

-- | Checks if a transaction is valid.
transactionIsValid ::
       BoolType (Bool context)
    => BlockId context
    -> Transaction context
    -> TransactionInputsWitness context
    -> Bool context
transactionIsValid s t w =
       transactionInputsAreValid s t w
    && transactionBalanceIsCorrect t
    && transactionContractsSucceed t