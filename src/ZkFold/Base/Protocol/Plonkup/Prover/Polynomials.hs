{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Prover.Polynomials where

import           Prelude                                 hiding (Num (..), drop, length, sum, take, (!!), (/), (^))

import           ZkFold.Base.Algebra.EllipticCurve.Class (EllipticCurve (..))
import           ZkFold.Base.Protocol.Plonkup.Internal   (PlonkupPolyExtended)

data PlonkupCircuitPolynomials n c = PlonkupCircuitPolynomials {
        ql     :: PlonkupPolyExtended n c,
        qr     :: PlonkupPolyExtended n c,
        qo     :: PlonkupPolyExtended n c,
        qm     :: PlonkupPolyExtended n c,
        qc     :: PlonkupPolyExtended n c,
        qk     :: PlonkupPolyExtended n c,
        sigma1 :: PlonkupPolyExtended n c,
        sigma2 :: PlonkupPolyExtended n c,
        sigma3 :: PlonkupPolyExtended n c
    }
instance Show (ScalarField c) => Show (PlonkupCircuitPolynomials n c) where
    show (PlonkupCircuitPolynomials ql qr qo qm qc qk sigma1 sigma2 sigma3) =
        "Circuit Polynomials: "
        ++ show ql ++ " "
        ++ show qr ++ " "
        ++ show qo ++ " "
        ++ show qm ++ " "
        ++ show qc ++ " "
        ++ show qk ++ " "
        ++ show sigma1 ++ " "
        ++ show sigma2 ++ " "
        ++ show sigma3
