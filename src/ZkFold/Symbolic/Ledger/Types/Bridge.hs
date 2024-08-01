module ZkFold.Symbolic.Ledger.Types.Bridge where

import           Prelude                             hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Ledger.Types.Basic
import           ZkFold.Symbolic.Ledger.Types.Hash   (Hash)
import           ZkFold.Symbolic.Ledger.Types.Output (Output)

data BridgeDirection = L1ToL2 | L2ToL1

data Bridge (direction :: BridgeDirection) context = Bridge
    { bridgeL1Assets :: List context (Output context)
    , bridgeL2Assets :: List context (Output context)
    }

bridgeState :: Bridge direction context -> Hash context
bridgeState = undefined
