{-# LANGUAGE TypeApplications #-}

module Main where

import           Prelude                                     hiding (Bool, Num (..), Fractional(..), (==), length, take, drop, replicate)

import           Tests.ArithmeticCircuit                     (specArithmeticCircuit)
import           Tests.Arithmetization                       (specArithmetization)
import           Tests.Field                                 (specField)
import           Tests.GroebnerBasis                         (specGroebner)
import           Tests.Group                                 (specAdditiveGroup)
import           Tests.NonInteractiveProof                   (specNonInteractiveProof)
import           Tests.Pairing                               (specPairing)
import           Tests.Permutations                          (specPermutations)
-- import           Tests.Plonk                                 (specPlonk)
-- import           Tests.Scripts.LockedByTxId                  (specLockedByTxId)
-- import           Tests.Univariate                            (specUnivariate)

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Algebra.EllipticCurve.Class
-- import           ZkFold.Base.Protocol.ARK.Plonk              (PlonkBS)
import           ZkFold.Base.Protocol.Commitment.KZG         (KZG)

main :: IO ()
main = do
    specArithmeticCircuit @(Zp BLS12_381_Scalar)

    -- specLockedByTxId

    specArithmetization @(Zp BLS12_381_Scalar)
    specGroebner

    specPermutations
    specField @Fr
    specField @Fq
    specField @Fq2
    specField @Fq6
    specField @Fq12
    specAdditiveGroup @(Point BLS12_381_G1)
    specAdditiveGroup @(Point BLS12_381_G2)
    specPairing @BLS12_381_G1 @BLS12_381_G2
    -- specUnivariate

    -- specNonInteractiveProof @(KZG BLS12_381_G1 BLS12_381_G2 BLS12_381_GT (Zp BLS12_381_Scalar) N32)
    -- specPlonk
    -- specNonInteractiveProof @PlonkBS

    putStrLn "\nAll tests passed!"
