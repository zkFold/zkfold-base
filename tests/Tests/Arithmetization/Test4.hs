{-# LANGUAGE TypeApplications #-}

module Tests.Arithmetization.Test4 (specArithmetization4) where

import           Data.Map                                    (fromList, keys)
import           Prelude                                     hiding (Bool, Eq (..), Num (..), Ord (..), (&&))
import qualified Prelude                                     as Haskell
import           Test.Hspec                                  (Spec, describe, it)
import           Test.QuickCheck                             (Testable (..), (==>))
import           Tests.NonInteractiveProof.Plonk             (PlonkBS)

import           ZkFold.Base.Algebra.Basic.Class             (FromConstant (..))
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (Fr)
import qualified ZkFold.Base.Data.Vector                     as V
import           ZkFold.Base.Data.Vector                     (Vector (..))
import           ZkFold.Base.Protocol.ARK.Plonk              (Plonk (..), PlonkProverSecret, PlonkWitnessInput (..))
import           ZkFold.Base.Protocol.ARK.Plonk.Internal     (getParams)
import           ZkFold.Base.Protocol.NonInteractiveProof    (NonInteractiveProof (..))
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit (..), acValue, applyArgs, compile)
import           ZkFold.Symbolic.Data.Bool                   (Bool (..), BoolType (..))
import           ZkFold.Symbolic.Data.Eq                     (Eq (..))

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
        plonk   = Plonk @32 omega k1 k2 (Vector @2 $ keys inputs) ac x
        setupP  = setupProve @PlonkBS plonk
        setupV  = setupVerify @PlonkBS plonk
        witness = (PlonkWitnessInput inputs, ps)
        (input, proof) = prove @PlonkBS setupP witness

    in verify @PlonkBS setupV input proof

specArithmetization4 :: Spec
specArithmetization4 = do
    describe "LockedByTxId arithmetization test 1" $ do
        it "should pass" $ property testSameValue
    describe "LockedByTxId arithmetization test 2" $ do
        it "should pass" $ property $ \x y -> x /= y ==> testDifferentValue x y
    describe "LockedByTxId ZKP test" $ do
        it "should pass" $ property testZKP
