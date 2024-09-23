module Main where

import           Control.Monad             (unless)
import           Prelude                   hiding (Bool, Fractional (..), Num (..), drop, length, replicate, take, (==))
import           System.Environment        (lookupEnv)
import           Tests.ArithmeticCircuit   (specArithmeticCircuit)
import           Tests.Arithmetization     (specArithmetization)
import           Tests.Binary              (specBinary)
import           Tests.Blake2b             (specBlake2b)
import           Tests.ByteString          (specByteString)
import           Tests.FFA                 (specFFA)
import           Tests.Field               (specField)
import           Tests.GroebnerBasis       (specGroebner)
import           Tests.Group               (specAdditiveGroup)
import           Tests.NonInteractiveProof (specNonInteractiveProof)
import           Tests.Pairing             (specPairing)
import           Tests.Permutations        (specPermutations)
import           Tests.Plonkup             (specPlonkup)
import           Tests.SHA2                (specSHA2, specSHA2Natural)
import           Tests.UInt                (specUInt)
import           Tests.Univariate          (specUnivariate)

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
    specFFA
    specByteString

    -- Arithmetic circuit
    specArithmeticCircuit

    -- Arithmetization
    specArithmetization

    -- Protocols
    specPlonkup
    specNonInteractiveProof

    -- Cryptography
    specSHA2Natural
    -- These tests are slow. Only run them locally by setting the environment variable FULL_SHA2
    fullTests <- lookupEnv "FULL_SHA2"
    unless (null fullTests) specSHA2

    --TODO: implement a proper blake2b test
    specBlake2b


    putStrLn "\nAll tests passed!"
