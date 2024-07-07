module ZkFold.Symbolic.Ledger.Types.Transaction where

import           Prelude                                hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Basic
import           ZkFold.Symbolic.Ledger.Types.Contract
import           ZkFold.Symbolic.Ledger.Types.Input     (Input)
import           ZkFold.Symbolic.Ledger.Types.OutputRef (TransactionId)
import           ZkFold.Symbolic.Ledger.Types.Output    (Output)
import           ZkFold.Symbolic.Ledger.Types.Value     (Value)

data Transaction backend = Transaction
    { txInputs           :: [Input backend]
    , txPublicInputs     :: [Input backend]
    , txOutputs          :: [Output backend]
    , txPublicOutputs    :: [Output backend]
    , txMint             :: [Value backend]
    , txContractData     :: [(ContractId backend, ContractData backend)]
    , txValidityInterval :: (UTCTime backend, UTCTime backend)
    }

txId :: Transaction backend -> TransactionId backend
txId = undefined