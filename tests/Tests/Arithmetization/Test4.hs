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
                                                              plonkVerifierInput)
import           ZkFold.Base.Protocol.ARK.Plonk.Internal     (getParams)
import           ZkFold.Base.Protocol.NonInteractiveProof    (NonInteractiveProof (..))
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit (..), acValue, applyArgs, compile)
import           ZkFold.Symbolic.Data.Bool                   (Bool (..), BoolType (..))
import           ZkFold.Symbolic.Data.Eq                     (Eq (..))

type N = 1

type C = BLS12_381_G1
type F = ScalarField C

lockedByTxId :: forall a b . (FromConstant a (b 1), Eq (Bool (b 1)) (b 1)) => a -> b 1 -> Bool (b 1)
lockedByTxId targetValue inputValue = inputValue == fromConstant targetValue

testSameValue :: F -> Haskell.Bool
testSameValue targetValue =
    let Bool ac = compile @F (lockedByTxId @F @(ArithmeticCircuit F) targetValue) :: Bool (ArithmeticCircuit F 1)
        b       = Bool $ acValue (applyArgs ac [targetValue])
    in b Haskell.== true

testDifferentValue :: F -> F -> Haskell.Bool
testDifferentValue targetValue otherValue =
    let Bool ac = compile @F (lockedByTxId @F @(ArithmeticCircuit F) targetValue) :: Bool (ArithmeticCircuit F 1)
        b       = Bool $ acValue (applyArgs ac [otherValue])
    in b Haskell.== false

testZKP :: F -> PlonkProverSecret C -> F -> Haskell.Bool
testZKP x ps targetValue =
    let Bool ac = compile @F (lockedByTxId @F @(ArithmeticCircuit F) targetValue) :: Bool (ArithmeticCircuit F 1)

        (omega, k1, k2) = getParams 32
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
        it "should pass" $ property $ \x y -> x Haskell./= y ==> testDifferentValue x y
    describe "LockedByTxId ZKP test" $ do
        it "should pass" $ withMaxSuccess 10 $ property testZKP
