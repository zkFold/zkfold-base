module ZkFold.Base.Protocol.Plonkup.Testing where

import           Prelude                                             hiding (Num (..), drop, length, pi, sum, take,
                                                                      (!!), (/), (^))

import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve(ScalarField))
import           ZkFold.Base.Algebra.Polynomials.Univariate          (PolyVec)
import           ZkFold.Base.Protocol.Plonkup.Internal               (PlonkupPolyExtended)

data PlonkupProverTestInfo n c1 = PlonkupProverTestInfo
    { omega         :: ScalarField c1
    , k1            :: ScalarField c1
    , k2            :: ScalarField c1
    , qlX           :: PlonkupPolyExtended n c1
    , qrX           :: PlonkupPolyExtended n c1
    , qoX           :: PlonkupPolyExtended n c1
    , qmX           :: PlonkupPolyExtended n c1
    , qcX           :: PlonkupPolyExtended n c1
    , aX            :: PlonkupPolyExtended n c1
    , bX            :: PlonkupPolyExtended n c1
    , cX            :: PlonkupPolyExtended n c1
    , piX           :: PlonkupPolyExtended n c1
    , s1X           :: PlonkupPolyExtended n c1
    , s2X           :: PlonkupPolyExtended n c1
    , s3X           :: PlonkupPolyExtended n c1
    , qkX           :: PlonkupPolyExtended n c1
    , tX            :: PlonkupPolyExtended n c1
    , z1X           :: PlonkupPolyExtended n c1
    , z2X           :: PlonkupPolyExtended n c1
    , fX            :: PlonkupPolyExtended n c1
    , h1X           :: PlonkupPolyExtended n c1
    , h2X           :: PlonkupPolyExtended n c1
    , zhX           :: PlonkupPolyExtended n c1
    , qX            :: PlonkupPolyExtended n c1
    , qlowX         :: PlonkupPolyExtended n c1
    , qmidX         :: PlonkupPolyExtended n c1
    , qhighX        :: PlonkupPolyExtended n c1
    , rX            :: PlonkupPolyExtended n c1
    , alpha         :: ScalarField c1
    , beta          :: ScalarField c1
    , gamma         :: ScalarField c1
    , delta         :: ScalarField c1
    , epsilon       :: ScalarField c1
    , xi            :: ScalarField c1
    , omegas        :: PolyVec (ScalarField c1) n
    , omegas'       :: PlonkupPolyExtended n c1
    , grandProduct1 :: PolyVec (ScalarField c1) n
    , w1            :: PolyVec (ScalarField c1) n
    , w2            :: PolyVec (ScalarField c1) n
    , w3            :: PolyVec (ScalarField c1) n
    }
