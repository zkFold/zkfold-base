module ZkFold.Symbolic.Ledger.Validation.Transaction where

import           Prelude                         hiding (Bool, Eq, length, splitAt, (*), (+), (==), (&&))

import           ZkFold.Symbolic.Data.Bool       (BoolType (..))
import           ZkFold.Symbolic.Ledger.Types

data TransactionInputsWitness backend

transactionInputsAreValid ::
       BlockId backend
    -> Transaction backend
    -> TransactionInputsWitness backend
    -> Bool backend
transactionInputsAreValid _ _ _ = undefined

transactionBalanceIsCorrect :: Transaction backend -> Bool a
transactionBalanceIsCorrect _ = undefined

transactionContractsSucceed :: Transaction backend -> Bool a
transactionContractsSucceed _ = undefined

transactionIsValid ::
       BoolType (Bool backend)
    => BlockId backend
    -> Transaction backend
    -> TransactionInputsWitness backend
    -> Bool backend
transactionIsValid s t w =
       transactionInputsAreValid s t w
    && transactionBalanceIsCorrect t
    && transactionContractsSucceed t