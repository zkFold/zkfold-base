module ZkFold.Symbolic.Ledger.Types.Transaction where

import           Prelude                                hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Contract
import           ZkFold.Symbolic.Ledger.Types.Input     (Input)
import           ZkFold.Symbolic.Ledger.Types.OutputRef (TransactionId)
import           ZkFold.Symbolic.Ledger.Types.Output    (Output)
import           ZkFold.Symbolic.Ledger.Types.Value     (Value)

data Transaction uint utc a = Transaction
    { txInputs           :: [Input uint a]
    , txPublicInputs     :: [Input uint a]
    , txOutputs          :: [Output uint a]
    , txPublicOutputs    :: [Output uint a]
    , txMint             :: [Value uint a]
    , txContractData     :: [(ContractId a, ContractData a)]
    , txValidityInterval :: (utc a, utc a)
    }

txId :: Transaction uint utc a -> TransactionId a
txId = undefined