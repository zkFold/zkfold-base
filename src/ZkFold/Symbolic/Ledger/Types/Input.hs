module ZkFold.Symbolic.Ledger.Types.Input where

import           Prelude                                hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Output    (Output)
import           ZkFold.Symbolic.Ledger.Types.OutputRef (OutputRef)

-- | Input to a transaction. Contains the reference to the output being spent and the output itself.
data Input context = Input
    { txiOutputRef :: OutputRef context
    , txiOutput    :: Output context
    }