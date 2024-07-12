{-# LANGUAGE TypeApplications #-}

module Tests.Arithmetization.Test4 (specArithmetization4) where

import           Data.Map                                    (fromList)
import           Prelude                                     hiding (Bool, Eq (..), Num (..), Ord (..), (&&))
import qualified Prelude                                     as Haskell
import           Test.Hspec                                  (Spec, describe, it)
import           Test.QuickCheck                             (Testable (..), withMaxSuccess, (==>))
import           Tests.NonInteractiveProof.Plonk             (PlonkBS)

import           ZkFold.Base.Algebra.Basic.Class             (FromConstant (..), one)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_G1)
import           ZkFold.Base.Algebra.EllipticCurve.Class     (EllipticCurve (..))
import qualified ZkFold.Base.Data.Vector                     as V
import           ZkFold.Base.Protocol.ARK.Plonk              (Plonk (..), PlonkProverSecret, PlonkWitnessInput (..),
                                                              plonkVerifierInput, PlonkInput(..))
import           ZkFold.Base.Protocol.ARK.Plonk.Internal     (getParams)
import           ZkFold.Base.Protocol.NonInteractiveProof    (NonInteractiveProof (..))
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit (..), acValue, applyArgs, compile)
import           ZkFold.Symbolic.Data.Bool                   (Bool (..), BoolType (..))
import           ZkFold.Symbolic.Data.Eq                     (Eq (..))

type N = 1

type C = BLS12_381_G1
type F = ScalarField C

lockedByTxId :: forall b a a' . (FromConstant a' (b 1 a), Eq (Bool (b 1 a)) (b 1 a)) => a' -> b 1 a -> Bool (b 1 a)
lockedByTxId targetValue inputValue = inputValue == fromConstant targetValue

testSameValue :: F -> Haskell.Bool
testSameValue targetValue =
    let Bool ac = compile @F (lockedByTxId @ArithmeticCircuit @F targetValue) :: Bool (ArithmeticCircuit 1 F)
        b       = Bool $ acValue (applyArgs ac [targetValue])
    in b == true

testDifferentValue :: F -> F -> Haskell.Bool
testDifferentValue targetValue otherValue =
    let Bool ac = compile @F (lockedByTxId @ArithmeticCircuit @F targetValue) :: Bool (ArithmeticCircuit 1 F)
        b       = Bool $ acValue (applyArgs ac [otherValue])
    in b == false

testOnlyOutputZKP :: F -> PlonkProverSecret C -> F -> Haskell.Bool
testOnlyOutputZKP x ps targetValue =
    let Bool ac = compile @F (lockedByTxId @ArithmeticCircuit @F targetValue) :: Bool (ArithmeticCircuit 1 F)

        (omega, k1, k2) = getParams 32
        witnessInputs   = fromList [(1, targetValue), (V.item $ acOutput ac, 1)]
        indexOutputBool = acOutput ac
        plonk   = Plonk @32 omega k1 k2 indexOutputBool ac x
        setupP  = setupProve @(PlonkBS N) plonk
        setupV  = setupVerify @(PlonkBS N) plonk
        witness = (PlonkWitnessInput witnessInputs, ps)
        (input, proof) = prove @(PlonkBS N) setupP witness

        -- `one` corresponds to `True`
        circuitOutputsTrue = plonkVerifierInput $ V.singleton one

    in unPlonkInput input == unPlonkInput circuitOutputsTrue && verify @(PlonkBS N) setupV circuitOutputsTrue proof

testOneInputZKP :: F -> PlonkProverSecret C -> F -> Haskell.Bool
testOneInputZKP x ps targetValue =
    let Bool ac = compile @F (lockedByTxId @ArithmeticCircuit @F targetValue) :: Bool (ArithmeticCircuit 1 F)

        (omega, k1, k2) = getParams 32
        witnessInputs  = fromList [(1, targetValue), (V.item $ acOutput ac, 1)]
        indexTargetValue = V.Vector [1]
        plonk   = Plonk @32 omega k1 k2 indexTargetValue ac x
        setupP  = setupProve @(PlonkBS N) plonk
        setupV  = setupVerify @(PlonkBS N) plonk
        witness = (PlonkWitnessInput witnessInputs, ps)
        (input, proof) = prove @(PlonkBS N) setupP witness

        onePublicInput = plonkVerifierInput $ V.singleton targetValue

    in unPlonkInput input == unPlonkInput onePublicInput && verify @(PlonkBS N) setupV onePublicInput proof

specArithmetization4 :: Spec
specArithmetization4 = do
    describe "LockedByTxId arithmetization test 1" $ do
        it "should pass" $ property testSameValue
    describe "LockedByTxId arithmetization test 2" $ do
        it "should pass" $ property $ \x y -> x /= y ==> testDifferentValue x y
    describe "LockedByTxId ZKP test only output" $ do
        it "should pass" $ withMaxSuccess 10 $ property testOnlyOutputZKP
    describe "LockedByTxId ZKP test one public input" $ do
       it "should pass" $ withMaxSuccess 10 $ property testOneInputZKP
