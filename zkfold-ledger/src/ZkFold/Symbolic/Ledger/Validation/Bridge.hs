module ZkFold.Symbolic.Ledger.Validation.Bridge where

import           Prelude                      hiding (Bool, Eq (..), all, length, splitAt, zip, (&&), (*), (+), (==))

import           ZkFold.Symbolic.Ledger.Types

bridgeIsValid ::
       Bridge L1ToL2 context
    -- ^ The bridged outputs from L1 to L2.
    -> Bridge L2ToL1 context
    -- ^ The bridged outputs from L2 to L1.
    -> Update context
    -- ^ The id of the latest valid update.
    -> Bool context
bridgeIsValid _ _ _ = undefined
