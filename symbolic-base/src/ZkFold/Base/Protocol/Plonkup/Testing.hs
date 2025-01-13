module ZkFold.Base.Protocol.Plonkup.Testing where

import           Prelude                                    hiding (Num (..), drop, length, pi, sum, take, (!!), (/),
                                                             (^))

import           ZkFold.Base.Algebra.Polynomials.Univariate (PolyVec)
import           ZkFold.Base.Protocol.Plonkup.Internal      (PlonkupPolyExtended)

data PlonkupProverTestInfo n f = PlonkupProverTestInfo
    { omega         :: f
    , k1            :: f
    , k2            :: f
    , qlX           :: PlonkupPolyExtended n f
    , qrX           :: PlonkupPolyExtended n f
    , qoX           :: PlonkupPolyExtended n f
    , qmX           :: PlonkupPolyExtended n f
    , qcX           :: PlonkupPolyExtended n f
    , aX            :: PlonkupPolyExtended n f
    , bX            :: PlonkupPolyExtended n f
    , cX            :: PlonkupPolyExtended n f
    , piX           :: PlonkupPolyExtended n f
    , s1X           :: PlonkupPolyExtended n f
    , s2X           :: PlonkupPolyExtended n f
    , s3X           :: PlonkupPolyExtended n f
    , qkX           :: PlonkupPolyExtended n f
    , tX            :: PlonkupPolyExtended n f
    , z1X           :: PlonkupPolyExtended n f
    , z2X           :: PlonkupPolyExtended n f
    , fX            :: PlonkupPolyExtended n f
    , h1X           :: PlonkupPolyExtended n f
    , h2X           :: PlonkupPolyExtended n f
    , zhX           :: PlonkupPolyExtended n f
    , qX            :: PlonkupPolyExtended n f
    , qlowX         :: PlonkupPolyExtended n f
    , qmidX         :: PlonkupPolyExtended n f
    , qhighX        :: PlonkupPolyExtended n f
    , rX            :: PlonkupPolyExtended n f
    , alpha         :: f
    , beta          :: f
    , gamma         :: f
    , delta         :: f
    , epsilon       :: f
    , xi            :: f
    , omegas        :: PolyVec f n
    , omegas'       :: PlonkupPolyExtended n f
    , grandProduct1 :: PolyVec f n
    , w1            :: PolyVec f n
    , w2            :: PolyVec f n
    , w3            :: PolyVec f n
    }
