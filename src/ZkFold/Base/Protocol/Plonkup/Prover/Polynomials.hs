{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Prover.Polynomials where

import           Prelude                                             hiding (Num (..), drop, length, sum, take, (!!),
                                                                      (/), (^))

import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..))
import           ZkFold.Base.Protocol.Plonkup.Internal               (PlonkPolyExtended)

data PlonkCircuitPolynomials n c = PlonkCircuitPolynomials {
        ql     :: PlonkPolyExtended n c,
        qr     :: PlonkPolyExtended n c,
        qo     :: PlonkPolyExtended n c,
        qm     :: PlonkPolyExtended n c,
        qc     :: PlonkPolyExtended n c,
        qk     :: PlonkPolyExtended n c,
        sigma1 :: PlonkPolyExtended n c,
        sigma2 :: PlonkPolyExtended n c,
        sigma3 :: PlonkPolyExtended n c
    }
instance Show (ScalarField c) => Show (PlonkCircuitPolynomials n c) where
    show (PlonkCircuitPolynomials ql qr qo qm qc qk sigma1 sigma2 sigma3) =
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
