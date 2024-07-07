module ZkFold.Symbolic.Ledger.Types.OutputRef where

import           Prelude                            hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Basic
import           ZkFold.Symbolic.Ledger.Types.Hash  (Hash)

type TransactionId a    = Hash a
type OutputIndex backend = UInt32 backend

data OutputRef backend = OutputRef
    { refId  :: TransactionId backend
    , refIdx :: OutputIndex backend
    }