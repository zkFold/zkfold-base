module Main where

import           Prelude                   hiding (Bool, Fractional (..), Num (..), drop, length, replicate, take, (==))
import           Tests.ArithmeticCircuit   (specArithmeticCircuit)
import           Tests.Arithmetization     (specArithmetization)
import           Tests.Binary              (specBinary)
import           Tests.Blake2b             (specBlake2b)
import           Tests.ByteString          (specByteString)
import           Tests.Compiler            (specCompiler)
import           Tests.EllipticCurve       (specEllipticCurve)
import           Tests.FFA                 (specFFA)
import           Tests.Field               (specField)
import           Tests.GroebnerBasis       (specGroebner)
import           Tests.Group               (specAdditiveGroup)
import           Tests.Hash                (specHash)
import           Tests.IVC                 (specIVC)
import           Tests.List                (specList)
import           Tests.NonInteractiveProof (specNonInteractiveProof)
import           Tests.Pairing             (specPairing)
import           Tests.Permutations        (specPermutations)
import           Tests.Plonkup             (specPlonkup)
import           Tests.RSA                 (specRSA)
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
    specEllipticCurve

    -- Compiler spec
    specCompiler

    -- Symbolic types and operations
    specHash
    specList
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
    specIVC

    -- Cryptography
    specSHA2Natural
    specSHA2
    specRSA
    specBlake2b

    putStrLn "\nAll tests passed!"
