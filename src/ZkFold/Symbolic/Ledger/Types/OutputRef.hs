module ZkFold.Symbolic.Ledger.Types.OutputRef where

import           Prelude                            hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Basic
import           ZkFold.Symbolic.Ledger.Types.Hash  (Hash)

-- | Transaction hash.
type TransactionId context = Hash context

-- | Index of an output in the transaction's output list.
type OutputIndex context   = UInt32 context

-- | Reference to a transaction output.
data OutputRef context = OutputRef
    { refId  :: TransactionId context
    -- ^ The transaction id of the transaction that produced the output.
    , refIdx :: OutputIndex context
    -- ^ The index of the output in the transaction's output list.
    }