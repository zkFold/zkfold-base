module ZkFold.Base.Protocol.Plonkup.Testing where

import           Prelude                                    hiding (Num (..), drop, length, pi, sum, take, (!!), (/),
                                                             (^))

import           ZkFold.Base.Algebra.EllipticCurve.Class    (CyclicGroup (ScalarFieldOf))
import           ZkFold.Base.Algebra.Polynomials.Univariate (PolyVec)
import           ZkFold.Base.Protocol.Plonkup.Internal      (PlonkupPolyExtended)

data PlonkupProverTestInfo n g1 = PlonkupProverTestInfo
    { omega         :: ScalarFieldOf g1
    , k1            :: ScalarFieldOf g1
    , k2            :: ScalarFieldOf g1
    , qlX           :: PlonkupPolyExtended n g1
    , qrX           :: PlonkupPolyExtended n g1
    , qoX           :: PlonkupPolyExtended n g1
    , qmX           :: PlonkupPolyExtended n g1
    , qcX           :: PlonkupPolyExtended n g1
    , aX            :: PlonkupPolyExtended n g1
    , bX            :: PlonkupPolyExtended n g1
    , cX            :: PlonkupPolyExtended n g1
    , piX           :: PlonkupPolyExtended n g1
    , s1X           :: PlonkupPolyExtended n g1
    , s2X           :: PlonkupPolyExtended n g1
    , s3X           :: PlonkupPolyExtended n g1
    , qkX           :: PlonkupPolyExtended n g1
    , tX            :: PlonkupPolyExtended n g1
    , z1X           :: PlonkupPolyExtended n g1
    , z2X           :: PlonkupPolyExtended n g1
    , fX            :: PlonkupPolyExtended n g1
    , h1X           :: PlonkupPolyExtended n g1
    , h2X           :: PlonkupPolyExtended n g1
    , zhX           :: PlonkupPolyExtended n g1
    , qX            :: PlonkupPolyExtended n g1
    , qlowX         :: PlonkupPolyExtended n g1
    , qmidX         :: PlonkupPolyExtended n g1
    , qhighX        :: PlonkupPolyExtended n g1
    , rX            :: PlonkupPolyExtended n g1
    , alpha         :: ScalarFieldOf g1
    , beta          :: ScalarFieldOf g1
    , gamma         :: ScalarFieldOf g1
    , delta         :: ScalarFieldOf g1
    , epsilon       :: ScalarFieldOf g1
    , xi            :: ScalarFieldOf g1
    , omegas        :: PolyVec (ScalarFieldOf g1) n
    , omegas'       :: PlonkupPolyExtended n g1
    , grandProduct1 :: PolyVec (ScalarFieldOf g1) n
    , w1            :: PolyVec (ScalarFieldOf g1) n
    , w2            :: PolyVec (ScalarFieldOf g1) n
    , w3            :: PolyVec (ScalarFieldOf g1) n
    }
