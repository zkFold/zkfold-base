{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Verifier.Commitments where

import           Prelude                                 hiding (Num (..), drop, length, sum, take, (!!), (/), (^))

import           ZkFold.Base.Algebra.EllipticCurve.Class (Point)

data PlonkupCircuitCommitments baseField = PlonkupCircuitCommitments {
        cmQl :: Point Bool baseField,
        cmQr :: Point Bool baseField,
        cmQo :: Point Bool baseField,
        cmQm :: Point Bool baseField,
        cmQc :: Point Bool baseField,
        cmQk :: Point Bool baseField,
        cmS1 :: Point Bool baseField,
        cmS2 :: Point Bool baseField,
        cmS3 :: Point Bool baseField,
        cmT1 :: Point Bool baseField
    }
instance (Show baseField) => Show (PlonkupCircuitCommitments baseField) where
    show PlonkupCircuitCommitments {..} =
        "Plonkup Circuit Commitments: "
        ++ show cmQl ++ " "
        ++ show cmQr ++ " "
        ++ show cmQo ++ " "
        ++ show cmQm ++ " "
        ++ show cmQc ++ " "
        ++ show cmQk ++ " "
        ++ show cmS1 ++ " "
        ++ show cmS2 ++ " "
        ++ show cmS3 ++ " "
        ++ show cmT1
