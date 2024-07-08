module ZkFold.Symbolic.Ledger.Validation.Transaction where

import           Prelude                         hiding (Bool, Eq, length, splitAt, (*), (+), (==), (&&))

import           ZkFold.Symbolic.Data.Bool       (BoolType (..))
import           ZkFold.Symbolic.Ledger.Types

data TransactionInputsWitness context

transactionInputsAreValid ::
       BlockId context
    -> Transaction context
    -> TransactionInputsWitness context
    -> Bool context
transactionInputsAreValid _ _ _ = undefined

transactionBalanceIsCorrect :: Transaction context -> Bool a
transactionBalanceIsCorrect _ = undefined

transactionContractsSucceed :: Transaction context -> Bool a
transactionContractsSucceed _ = undefined

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