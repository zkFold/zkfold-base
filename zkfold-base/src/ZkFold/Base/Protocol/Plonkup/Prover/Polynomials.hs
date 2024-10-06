{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Prover.Polynomials where

import           Prelude                                 hiding (Num (..), drop, length, sum, take, (!!), (/), (^))

import           ZkFold.Base.Algebra.EllipticCurve.Class (EllipticCurve (..))
import           ZkFold.Base.Protocol.Plonkup.Internal   (PlonkupPolyExtended)

data PlonkupCircuitPolynomials n c = PlonkupCircuitPolynomials {
        qlX :: PlonkupPolyExtended n c,
        qrX :: PlonkupPolyExtended n c,
        qoX :: PlonkupPolyExtended n c,
        qmX :: PlonkupPolyExtended n c,
        qcX :: PlonkupPolyExtended n c,
        qkX :: PlonkupPolyExtended n c,
        s1X :: PlonkupPolyExtended n c,
        s2X :: PlonkupPolyExtended n c,
        s3X :: PlonkupPolyExtended n c,
        tX  :: PlonkupPolyExtended n c
    }
instance Show (ScalarField c) => Show (PlonkupCircuitPolynomials n c) where
    show PlonkupCircuitPolynomials {..} =
        "Circuit Polynomials: "
        ++ show qlX ++ " "
        ++ show qrX ++ " "
        ++ show qoX ++ " "
        ++ show qmX ++ " "
        ++ show qcX ++ " "
        ++ show qkX ++ " "
        ++ show s1X ++ " "
        ++ show s2X ++ " "
        ++ show s3X
