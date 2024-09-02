{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Verifier.Commitments where

import           Prelude                                 hiding (Num (..), drop, length, sum, take, (!!), (/), (^))

import           ZkFold.Base.Algebra.EllipticCurve.Class (EllipticCurve (..), Point)

data PlonkupCircuitCommitments c = PlonkupCircuitCommitments {
        cmQl :: Point c,
        cmQr :: Point c,
        cmQo :: Point c,
        cmQm :: Point c,
        cmQc :: Point c,
        cmQk :: Point c,
        cmS1 :: Point c,
        cmS2 :: Point c,
        cmS3 :: Point c
    }
instance (Show (BaseField c), EllipticCurve c) => Show (PlonkupCircuitCommitments c) where
    show (PlonkupCircuitCommitments cmQl cmQr cmQo cmQm cmQc cmQk cmS1 cmS2 cmS3) =
        "Plonkup Circuit Commitments: "
        ++ show cmQl ++ " "
        ++ show cmQr ++ " "
        ++ show cmQo ++ " "
        ++ show cmQm ++ " "
        ++ show cmQc ++ " "
        ++ show cmQk ++ " "
        ++ show cmS1 ++ " "
        ++ show cmS2 ++ " "
        ++ show cmS3