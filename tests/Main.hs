module Main where

import           Prelude                                     hiding (Bool, Fractional (..), Num (..), drop, length,
                                                              replicate, take, (==))
import           Tests.ArithmeticCircuit                     (specArithmeticCircuit)
import           Tests.Arithmetization                       (specArithmetization)
import           Tests.Binary                                (specBinary)
import           Tests.ByteString                            (specByteString)
import           Tests.Field                                 (specField)
import           Tests.GroebnerBasis                         (specGroebner)
import           Tests.Group                                 (specAdditiveGroup)
import           Tests.NonInteractiveProof                   (specNonInteractiveProof)
import           Tests.Pairing                               (specPairing)
import           Tests.Permutations                          (specPermutations)
import           Tests.Plonk                                 (specPlonk)
import           Tests.SHA2                                  (specSHA2Natural)
import           Tests.UInt                                  (specUInt)
import           Tests.Univariate                            (specUnivariate)

main :: IO ()
main = do
    -- Base
    specBinary

    -- Algebra
    specPermutations
    specField
    specAdditiveGroup
    specPairing
    specUnivariate
    specGroebner

    -- Symbolic types and operations
    specUInt
    specByteString
    --TODO: optimise eval and uncomment this test
    -- specSHA2

    -- Arithmetic circuit
    specArithmetization
    specArithmeticCircuit

    -- Non-interactive proofs
    specNonInteractiveProof
    specPlonk

    -- Cryptography
    specSHA2Natural

    putStrLn "\nAll tests passed!"
