module ZkFold.Symbolic.Ledger.Validation.Transaction where

import           Prelude                         hiding (Bool, Eq, length, splitAt, (*), (+), (==), (&&))

import           ZkFold.Base.Algebra.Basic.Class (Ring)
import           ZkFold.Symbolic.Data.Bool       (Bool, BoolType (..))
import           ZkFold.Symbolic.Ledger.Types    (Transaction, LedgerState)

type TransactionInputsWitness a = a

transactionInputsAreValid ::
       LedgerState a
    -> Transaction a
    -> TransactionInputsWitness a
    -> Bool a
transactionInputsAreValid _ _ _ = undefined

transactionBalanceIsCorrect :: Transaction a -> Bool a
transactionBalanceIsCorrect _ = undefined

transactionContractsSucceed :: Transaction a -> Bool a
transactionContractsSucceed _ = undefined

transactionIsValid ::
       Ring a
    => LedgerState a
    -> Transaction a
    -> TransactionInputsWitness a
    -> Bool a
transactionIsValid s t w =
       transactionInputsAreValid s t w
    && transactionBalanceIsCorrect t
    && transactionContractsSucceed t