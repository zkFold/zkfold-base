module ZkFold.Symbolic.Ledger.Types.OutputRef where

import           Prelude                           hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Hash (Hash)

type TransactionId a    = Hash a
type OutputIndex uint a = uint a

data OutputRef uint a = OutputRef
    { refId  :: TransactionId a
    , refIdx :: OutputIndex uint a
    }