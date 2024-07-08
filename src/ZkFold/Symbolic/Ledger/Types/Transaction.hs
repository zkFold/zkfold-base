module ZkFold.Symbolic.Ledger.Types.Transaction where

import           Prelude                                hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Basic
import           ZkFold.Symbolic.Ledger.Types.Contract
import           ZkFold.Symbolic.Ledger.Types.Input     (Input)
import           ZkFold.Symbolic.Ledger.Types.OutputRef (TransactionId)
import           ZkFold.Symbolic.Ledger.Types.Output    (Output)
import           ZkFold.Symbolic.Ledger.Types.Value     (Value)

-- | zkFold ledger transaction.
data Transaction context = Transaction
    { txInputs           :: [Input context]
    -- A list of inputs to the transaction.
    , txPublicInputs     :: [Input context]
    -- A list of public inputs to the transaction.
    , txOutputs          :: [Output context]
    -- A list of outputs of the transaction.
    , txPublicOutputs    :: [Output context]
    -- A list of public outputs of the transaction.
    , txMint             :: [Value context]
    -- A list of minted values.
    , txContractData     :: [(ContractId context, ContractData context)]
    -- A list of contract data items.
    , txValidityInterval :: (UTCTime context, UTCTime context)
    -- The validity interval of the transaction.
    }

txId :: Transaction context -> TransactionId context
txId = undefined