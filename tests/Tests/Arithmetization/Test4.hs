{-# LANGUAGE TypeApplications #-}

module Tests.Arithmetization.Test4 (specArithmetization4) where

import           Data.Map                                    (fromList)
import           Prelude                                     hiding (Bool, Eq (..), Num (..), Ord (..), (&&))
import qualified Prelude                                     as Haskell
import           Test.Hspec                                  (Spec, describe, it)
import           Test.QuickCheck                             (Testable (..), withMaxSuccess, (==>))
import           Tests.NonInteractiveProof.Plonk             (PlonkBS)

import           ZkFold.Base.Algebra.Basic.Class             (FromConstant (..), one)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (Fr)
import qualified ZkFold.Base.Data.Vector                     as V
import           ZkFold.Base.Protocol.ARK.Plonk              (Plonk (..), PlonkProverSecret, PlonkWitnessInput (..),
                                                              plonkVerifierInput)
import           ZkFold.Base.Protocol.ARK.Plonk.Internal     (getParams)
import           ZkFold.Base.Protocol.NonInteractiveProof    (NonInteractiveProof (..))
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit (..), acValue, applyArgs, compile)
import           ZkFold.Symbolic.Data.Bool                   (Bool (..), BoolType (..))
import           ZkFold.Symbolic.Data.Eq                     (Eq (..))

type N = 1

lockedByTxId :: forall b a a' . (FromConstant a' (b 1 a), Eq (Bool (b 1 a)) (b 1 a)) => a' -> (b 1 a) -> Bool (b 1 a)
lockedByTxId targetValue inputValue = inputValue == fromConstant targetValue

testSameValue :: Fr -> Haskell.Bool
testSameValue targetValue =
    let Bool ac = compile @Fr (lockedByTxId @ArithmeticCircuit @Fr targetValue) :: Bool (ArithmeticCircuit 1 Fr)
        b       = Bool $ acValue (applyArgs ac [targetValue])
    in b == true

testDifferentValue :: Fr -> Fr -> Haskell.Bool
testDifferentValue targetValue otherValue =
    let Bool ac = compile @Fr (lockedByTxId @ArithmeticCircuit @Fr targetValue) :: Bool (ArithmeticCircuit 1 Fr)
        b       = Bool $ acValue (applyArgs ac [otherValue])
    in b == false

testZKP :: Fr -> PlonkProverSecret -> Fr -> Haskell.Bool
testZKP x ps targetValue =
    let Bool ac = compile @Fr (lockedByTxId @ArithmeticCircuit @Fr targetValue) :: Bool (ArithmeticCircuit 1 Fr)

        (omega, k1, k2) = getParams 5
        inputs  = fromList [(1, targetValue), (V.item $ acOutput ac, 1)]
        plonk   = Plonk @32 omega k1 k2 (acOutput ac) ac x
        setupP  = setupProve @(PlonkBS N) plonk
        setupV  = setupVerify @(PlonkBS N) plonk
        witness = (PlonkWitnessInput inputs, ps)
        (_, proof) = prove @(PlonkBS N) setupP witness

        -- `one` corresponds to `True`
        circuitOutputsTrue = plonkVerifierInput $ V.singleton one

    in verify @(PlonkBS N) setupV circuitOutputsTrue proof

specArithmetization4 :: Spec
specArithmetization4 = do
    describe "LockedByTxId arithmetization test 1" $ do
        it "should pass" $ property testSameValue
    describe "LockedByTxId arithmetization test 2" $ do
        it "should pass" $ property $ \x y -> x /= y ==> testDifferentValue x y
    describe "LockedByTxId ZKP test" $ do
        it "should pass" $ withMaxSuccess 10 $ property testZKP
