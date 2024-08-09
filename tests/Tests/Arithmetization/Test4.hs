{-# LANGUAGE TypeApplications #-}

module Tests.Arithmetization.Test4 (specArithmetization4) where

import           GHC.Generics                                (Par1 (unPar1))
import           GHC.Num                                     (Natural)
import           Prelude                                     hiding (Bool, Eq (..), Num (..), Ord (..), (&&))
import qualified Prelude                                     as Haskell
import           Test.Hspec                                  (Spec, describe, it)
import           Test.QuickCheck                             (Testable (..), withMaxSuccess, (==>))
import           Tests.NonInteractiveProof.Plonk             (PlonkBS)

import           ZkFold.Base.Algebra.Basic.Class             (FromConstant (..), one, zero, (+))
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_G1)
import           ZkFold.Base.Algebra.EllipticCurve.Class     (EllipticCurve (..))
import qualified ZkFold.Base.Data.Vector                     as V
import           ZkFold.Base.Protocol.ARK.Plonk              (Plonk (..), PlonkInput (..), PlonkProverSecret,
                                                              PlonkWitnessInput (..), plonkVerifierInput)
import           ZkFold.Base.Protocol.ARK.Plonk.Internal     (getParams)
import           ZkFold.Base.Protocol.NonInteractiveProof    (NonInteractiveProof (..))
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit (..), compile,
                                                              compileForceOne, eval)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (Var (..))
import           ZkFold.Symbolic.Data.Bool                   (Bool (..))
import           ZkFold.Symbolic.Data.Eq                     (Eq (..))
import           ZkFold.Symbolic.Data.FieldElement           (FieldElement)

type N = 1

type C = BLS12_381_G1
type F = ScalarField C

lockedByTxId :: forall a c . (FromConstant a (FieldElement c), Symbolic c) => a -> FieldElement c -> Bool c
lockedByTxId targetValue inputValue = inputValue == fromConstant targetValue

testSameValue :: F -> Haskell.Bool
testSameValue targetValue =
    let Bool ac = compile @1 @F (lockedByTxId @F @(ArithmeticCircuit F (V.Vector 1)) targetValue) :: Bool (ArithmeticCircuit F (V.Vector 1))
        b       = unPar1 (eval ac (V.singleton targetValue))
    in b Haskell.== one

testDifferentValue :: F -> F -> Haskell.Bool
testDifferentValue targetValue otherValue =
    let Bool ac = compile @1 @F (lockedByTxId @F @(ArithmeticCircuit F (V.Vector 1)) targetValue) :: Bool (ArithmeticCircuit F (V.Vector 1))
        b       = unPar1 (eval ac (V.singleton otherValue))
    in b Haskell.== zero

testOnlyOutputZKP :: F -> PlonkProverSecret C -> F -> Haskell.Bool
testOnlyOutputZKP x ps targetValue =
    let Bool ac = compile @1 @F (lockedByTxId @F @(ArithmeticCircuit F (V.Vector 1)) targetValue) :: Bool (ArithmeticCircuit F (V.Vector 1))

        (omega, k1, k2) = getParams 32
        witnessInputs = V.singleton targetValue
        varF (NewVar ix) = ix + 1
        varF (InVar ix) = fromIntegral ix
        indexOutputBool = V.singleton $ varF $ unPar1 $ acOutput ac
        plonk   = Plonk @32 omega k1 k2 indexOutputBool ac x
        setupP  = setupProve @(PlonkBS N) plonk
        setupV  = setupVerify @(PlonkBS N) plonk
        witness = (PlonkWitnessInput witnessInputs, ps)
        (input, proof) = prove @(PlonkBS N) setupP witness

        -- `one` corresponds to `True`
        circuitOutputsTrue = plonkVerifierInput $ V.singleton one

    in unPlonkInput input Haskell.== unPlonkInput circuitOutputsTrue Haskell.&& verify @(PlonkBS N) setupV circuitOutputsTrue proof

testSafeOneInputZKP :: F -> PlonkProverSecret C -> F -> Haskell.Bool
testSafeOneInputZKP x ps targetValue =
    let Bool ac = compileForceOne @1 @F (lockedByTxId @F @(ArithmeticCircuit F (V.Vector 1)) targetValue) :: Bool (ArithmeticCircuit F (V.Vector 1))

        (omega, k1, k2) = getParams 32
        witnessInputs  = V.singleton targetValue
        indexTargetValue = V.singleton (1 :: Natural)
        plonk   = Plonk @32 omega k1 k2 indexTargetValue ac x
        setupP  = setupProve @(PlonkBS N) plonk
        setupV  = setupVerify @(PlonkBS N) plonk
        witness = (PlonkWitnessInput witnessInputs, ps)
        (input, proof) = prove @(PlonkBS N) setupP witness

        onePublicInput = plonkVerifierInput $ V.singleton targetValue

    in unPlonkInput input Haskell.== unPlonkInput onePublicInput Haskell.&& verify @(PlonkBS N) setupV onePublicInput proof

testAttackSafeOneInputZKP :: F -> PlonkProverSecret C -> F -> Haskell.Bool
testAttackSafeOneInputZKP x ps targetValue =
    let Bool ac = compileForceOne @1 @F (lockedByTxId @F @(ArithmeticCircuit F (V.Vector 1)) targetValue) :: Bool (ArithmeticCircuit F (V.Vector 1))

        (omega, k1, k2) = getParams 32
        witnessInputs  = V.singleton (targetValue + 1)
        indexTargetValue = V.singleton (1 :: Natural)
        plonk   = Plonk @32 omega k1 k2 indexTargetValue ac x
        setupP  = setupProve @(PlonkBS N) plonk
        setupV  = setupVerify @(PlonkBS N) plonk
        witness = (PlonkWitnessInput witnessInputs, ps)
        (input, proof) = prove @(PlonkBS N) setupP witness

        onePublicInput = plonkVerifierInput $ V.singleton $ targetValue + 1

    in unPlonkInput input Haskell.== unPlonkInput onePublicInput Haskell.&& Haskell.not (verify @(PlonkBS N) setupV onePublicInput proof)

specArithmetization4 :: Spec
specArithmetization4 = do
    describe "LockedByTxId arithmetization test 1" $ do
        it "should pass" $ property testSameValue
    describe "LockedByTxId arithmetization test 2" $ do
        it "should pass" $ property $ \x y -> x Haskell./= y ==> testDifferentValue x y
    describe "LockedByTxId ZKP test only output" $ do
        it "should pass" $ withMaxSuccess 10 $ property testOnlyOutputZKP
    describe "LockedByTxId ZKP test safe one public input" $ do
       it "should pass" $ withMaxSuccess 10 $ property testSafeOneInputZKP
    describe "LockedByTxId ZKP test attack safe one public input" $ do
       it "should pass" $ withMaxSuccess 10 $ property testAttackSafeOneInputZKP
