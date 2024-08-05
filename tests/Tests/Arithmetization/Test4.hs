{-# LANGUAGE TypeApplications #-}

module Tests.Arithmetization.Test4 (specArithmetization4) where

import           Data.Map                                    (fromList)
import           GHC.Generics                                (Par1 (unPar1))
import           Prelude                                     hiding (Bool, Eq (..), Num (..), Ord (..), (&&))
import qualified Prelude                                     as Haskell
import           Test.Hspec                                  (Spec, describe, it)
import           Test.QuickCheck                             (Testable (..), withMaxSuccess, (==>))
import           Tests.NonInteractiveProof.Plonk             (PlonkBS)

import           ZkFold.Base.Algebra.Basic.Class             (FromConstant (..), one, zero)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_G1)
import           ZkFold.Base.Algebra.EllipticCurve.Class     (EllipticCurve (..))
import qualified ZkFold.Base.Data.Vector                     as V
import           ZkFold.Base.Protocol.ARK.Plonk              (Plonk (..), PlonkProverSecret, PlonkWitnessInput (..),
                                                              plonkVerifierInput)
import           ZkFold.Base.Protocol.ARK.Plonk.Internal     (getParams)
import           ZkFold.Base.Protocol.NonInteractiveProof    (NonInteractiveProof (..))
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit (..), acValue, applyArgs, compile)
import           ZkFold.Symbolic.Data.Bool                   (Bool (..))
import           ZkFold.Symbolic.Data.Eq                     (Eq (..))
import           ZkFold.Symbolic.Data.FieldElement           (FieldElement)
import           ZkFold.Symbolic.Class

type N = 1

type C = BLS12_381_G1
type F = ScalarField C

lockedByTxId :: forall a c . (FromConstant a (FieldElement c), Symbolic c) => a -> FieldElement c -> Bool c
lockedByTxId targetValue inputValue = inputValue == fromConstant targetValue

testSameValue :: F -> Haskell.Bool
testSameValue targetValue =
    let Bool ac = compile @F (lockedByTxId @F @(ArithmeticCircuit F) targetValue) :: Bool (ArithmeticCircuit F)
        b       = unPar1 $ acValue (applyArgs ac [targetValue])
    in b Haskell.== one

testDifferentValue :: F -> F -> Haskell.Bool
testDifferentValue targetValue otherValue =
    let Bool ac = compile @F (lockedByTxId @F @(ArithmeticCircuit F) targetValue) :: Bool (ArithmeticCircuit F)
        b       = unPar1 $ acValue (applyArgs ac [otherValue])
    in b Haskell.== zero

testZKP :: F -> PlonkProverSecret C -> F -> Haskell.Bool
testZKP x ps targetValue =
    let Bool ac = compile @F (lockedByTxId @F @(ArithmeticCircuit F) targetValue) :: Bool (ArithmeticCircuit F)

        (omega, k1, k2) = getParams 32
        inputs  = fromList [(1, targetValue), (unPar1 $ acOutput ac, 1)]
        plonk   = Plonk @32 omega k1 k2 (V.singleton $ unPar1 $ acOutput ac) ac x
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
