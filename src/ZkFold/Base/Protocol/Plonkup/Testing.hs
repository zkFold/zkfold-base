module ZkFold.Base.Protocol.Plonkup.Testing where

import           Prelude                                             hiding (Num (..), drop, length, pi, sum, take,
                                                                      (!!), (/), (^))

import           ZkFold.Base.Protocol.Plonkup.Internal               (PlonkupPolyExtended)

data PlonkupProverTestInfo n c1 = PlonkupProverTestInfo
    { qlX :: PlonkupPolyExtended n c1
    , qrX :: PlonkupPolyExtended n c1
    , qoX :: PlonkupPolyExtended n c1
    , qmX :: PlonkupPolyExtended n c1
    , qcX :: PlonkupPolyExtended n c1
    , aX  :: PlonkupPolyExtended n c1
    , bX  :: PlonkupPolyExtended n c1
    , cX  :: PlonkupPolyExtended n c1
    , piX :: PlonkupPolyExtended n c1
    }