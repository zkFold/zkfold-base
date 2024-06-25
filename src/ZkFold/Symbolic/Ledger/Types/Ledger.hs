module ZkFold.Symbolic.Ledger.Types.Ledger where

import           Prelude                                  hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Data.UTCTime             (UTCTime)
import           ZkFold.Symbolic.Ledger.Types.Contract    (ContractId, ContractData)
import           ZkFold.Symbolic.Ledger.Types.Input       (Input)
import           ZkFold.Symbolic.Ledger.Types.OutputRef   (TransactionId)

type LedgerState a = a

data LedgerUpdate a = LedgerUpdate
    { luStartTime    :: UTCTime a
    , luEndTime      :: UTCTime a
    , luTransactions :: [(ContractId a, TransactionId a)]
    , luPublicInputs :: [(ContractId a, Input a)]
    , luContractData :: [(ContractId a, ContractData a)]
    }