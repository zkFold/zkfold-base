module ZkFold.Symbolic.Ledger.Types.Transaction where

import           Prelude                                hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Data.UTCTime
import           ZkFold.Symbolic.Ledger.Types.Contract
import           ZkFold.Symbolic.Ledger.Types.Input     (Input)
import           ZkFold.Symbolic.Ledger.Types.OutputRef (TransactionId)
import           ZkFold.Symbolic.Ledger.Types.Output    (Output)
import           ZkFold.Symbolic.Ledger.Types.Value     (Value)

data Transaction a = Transaction
    { txInputs           :: [Input a]
    , txPublicInputs     :: [Input a]
    , txOutputs          :: [Output a]
    , txPublicOutputs    :: [Output a]
    , txMint             :: [Value a]
    , txContractData     :: [ContractData a]
    , txValidityInterval :: (UTCTime a, UTCTime a)
    }

txId :: Transaction a -> TransactionId a
txId = undefined