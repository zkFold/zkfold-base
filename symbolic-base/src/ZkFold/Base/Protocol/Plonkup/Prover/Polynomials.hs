{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Prover.Polynomials where

import           Prelude                                 hiding (Num (..), drop, length, sum, take, (!!), (/), (^))

import           ZkFold.Base.Protocol.Plonkup.Internal   (PlonkupPolyExtended)

data PlonkupCircuitPolynomials n f = PlonkupCircuitPolynomials {
        qlX :: PlonkupPolyExtended n f,
        qrX :: PlonkupPolyExtended n f,
        qoX :: PlonkupPolyExtended n f,
        qmX :: PlonkupPolyExtended n f,
        qcX :: PlonkupPolyExtended n f,
        qkX :: PlonkupPolyExtended n f,
        s1X :: PlonkupPolyExtended n f,
        s2X :: PlonkupPolyExtended n f,
        s3X :: PlonkupPolyExtended n f,
        tX  :: PlonkupPolyExtended n f
    }
instance Show f => Show (PlonkupCircuitPolynomials n f) where
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
