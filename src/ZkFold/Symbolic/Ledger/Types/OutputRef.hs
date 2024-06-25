module ZkFold.Symbolic.Ledger.Types.OutputRef where

import           Prelude                   hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Data.UInt (UInt)

type TransactionId a = a
type OutputIndex a   = UInt 32 a

data OutputRef a = OutputRef
    { refId  :: TransactionId a
    , refIdx :: OutputIndex a
    }