module ZkFold.Symbolic.Ledger.Types.OutputRef where

import           Prelude                            hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Basic
import           ZkFold.Symbolic.Ledger.Types.Hash  (Hash)

type TransactionId context = Hash context
type OutputIndex context   = UInt32 context

data OutputRef context = OutputRef
    { refId  :: TransactionId context
    , refIdx :: OutputIndex context
    }