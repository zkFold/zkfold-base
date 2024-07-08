module ZkFold.Symbolic.Ledger.Types.Transaction where

import           Prelude                                hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Basic
import           ZkFold.Symbolic.Ledger.Types.Contract
import           ZkFold.Symbolic.Ledger.Types.Input     (Input)
import           ZkFold.Symbolic.Ledger.Types.OutputRef (TransactionId)
import           ZkFold.Symbolic.Ledger.Types.Output    (Output)
import           ZkFold.Symbolic.Ledger.Types.Value     (Value)

data Transaction context = Transaction
    { txInputs           :: [Input context]
    , txPublicInputs     :: [Input context]
    , txOutputs          :: [Output context]
    , txPublicOutputs    :: [Output context]
    , txMint             :: [Value context]
    , txContractData     :: [(ContractId context, ContractData context)]
    , txValidityInterval :: (UTCTime context, UTCTime context)
    }

txId :: Transaction context -> TransactionId context
txId = undefined