module ZkFold.Symbolic.Ledger.Types.Input where

import           Prelude                                hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Output    (Output)
import           ZkFold.Symbolic.Ledger.Types.OutputRef (OutputRef)

data Input a = Input
    { txiOutputRef :: OutputRef a
    , txiOutput    :: Output a
    }