{-# LANGUAGE TypeApplications #-}

module Main where

import           Prelude                                     hiding (Bool, Num (..), Fractional(..), (==), length, take, drop, replicate)

import           Tests.Arithmetization                       (specArithmetization)
import           Tests.Field                                 (specField)
import           Tests.GroebnerBasis                         (specGroebner)
import           Tests.Group                                 (specAdditiveGroup)
import           Tests.NonInteractiveProof                   (specNonInteractiveProof)
import           Tests.Pairing                               (specPairing)
import           Tests.Permutations                          (specPermutations)
import           Tests.Plonk                                 (specPlonk)
import           Tests.Scripts.LockedByTxId                  (specLockedByTxId)
import           Tests.Univariate                            (specUnivariate)

import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (Fr, Fq, Fq2, Fq6, Fq12)
import           ZkFold.Base.Protocol.ARK.Plonk              (Plonk)
import           ZkFold.Base.Protocol.Commitment.KZG         (KZG, G1, G2)

main :: IO ()
main = do
    specLockedByTxId

    specArithmetization @Fr
    specGroebner

    specPermutations
    specField @Fr
    specField @Fq
    specField @Fq2
    specField @Fq6
    specField @Fq12
    specAdditiveGroup @G1
    specAdditiveGroup @G2
    specPairing
    specUnivariate

    specNonInteractiveProof @KZG
    specPlonk
    specNonInteractiveProof @Plonk

    putStrLn "\nAll tests passed!"