module ZkFold.Symbolic.Ledger.Validation.Transaction where

import           Prelude                         hiding (Bool, Eq, length, splitAt, (*), (+), (==), (&&))

import           ZkFold.Symbolic.Data.Bool       (Bool, BoolType (..))
import           ZkFold.Symbolic.Ledger.Types

type TransactionInputsWitness a = a

transactionInputsAreValid ::
       BlockId a
    -> Transaction uint utc a
    -> TransactionInputsWitness a
    -> Bool a
transactionInputsAreValid _ _ _ = undefined

transactionBalanceIsCorrect :: Transaction uint utc a -> Bool a
transactionBalanceIsCorrect _ = undefined

transactionContractsSucceed :: Transaction uint utc a -> Bool a
transactionContractsSucceed _ = undefined

transactionIsValid ::
       BoolType (Bool a)
    => BlockId a
    -> Transaction uint utc a
    -> TransactionInputsWitness a
    -> Bool a
transactionIsValid s t w =
       transactionInputsAreValid s t w
    && transactionBalanceIsCorrect t
    && transactionContractsSucceed t