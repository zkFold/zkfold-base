{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.Arithmetization.Test4 (specArithmetization4) where

import           GHC.Generics                                        (Par1 (unPar1))
import           Prelude                                             hiding (Bool, Eq (..), Num (..), Ord (..), (&&))
import qualified Prelude                                             as Haskell
import           Test.Hspec                                          (Spec, describe, it)
import           Test.QuickCheck                                     (Testable (..), withMaxSuccess, (==>))
import           Tests.NonInteractiveProof.Plonkup                   (PlonkBS)

import           ZkFold.Base.Algebra.Basic.Class                     (FromConstant (..), one, zero, (+))
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381         (BLS12_381_G1)
import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..))
import qualified ZkFold.Base.Data.Vector                             as V
import           ZkFold.Base.Protocol.NonInteractiveProof            (CoreFunction, HaskellCore,
                                                                      NonInteractiveProof (..))
import           ZkFold.Base.Protocol.Plonkup
import           ZkFold.Base.Protocol.Plonkup.Input
import           ZkFold.Base.Protocol.Plonkup.Prover
import           ZkFold.Base.Protocol.Plonkup.Utils                  (getParams)
import           ZkFold.Base.Protocol.Plonkup.Witness
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler                            (ArithmeticCircuit (..), compile, compileForceOne,
                                                                      eval, witnessGenerator)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (Var (..))
import           ZkFold.Symbolic.Data.Bool                           (Bool (..))
import           ZkFold.Symbolic.Data.Eq                             (Eq (..))
import           ZkFold.Symbolic.Data.FieldElement                   (FieldElement)

type N = 1

type C = BLS12_381_G1
type F = ScalarField C

lockedByTxId :: forall a c . (FromConstant a (FieldElement c), Symbolic c) => a -> FieldElement c -> Bool c
lockedByTxId targetValue inputValue = inputValue == fromConstant targetValue

testSameValue :: F -> Haskell.Bool
testSameValue targetValue =
    let Bool ac = compile @F (lockedByTxId @F @(ArithmeticCircuit F (V.Vector 1)) targetValue) :: Bool (ArithmeticCircuit F (V.Vector 1))
        b       = unPar1 (eval ac (V.singleton targetValue))
    in b Haskell.== one

testDifferentValue :: F -> F -> Haskell.Bool
testDifferentValue targetValue otherValue =
    let Bool ac = compile @F (lockedByTxId @F @(ArithmeticCircuit F (V.Vector 1)) targetValue) :: Bool (ArithmeticCircuit F (V.Vector 1))
        b       = unPar1 (eval ac (V.singleton otherValue))
    in b Haskell.== zero

testOnlyOutputZKP :: forall core . (CoreFunction C core) => F -> PlonkupProverSecret C -> F -> Haskell.Bool
testOnlyOutputZKP x ps targetValue =
    let Bool ac = compile @F (lockedByTxId @F @(ArithmeticCircuit F (V.Vector 1)) targetValue) :: Bool (ArithmeticCircuit F (V.Vector 1))

        (omega, k1, k2) = getParams 32
        witnessInputs = V.singleton targetValue
        witnessNewVars = witnessGenerator ac witnessInputs
        indexOutputBool = V.singleton $ unPar1 $ acOutput ac
        plonk   = Plonkup @1 @32 omega k1 k2 indexOutputBool ac x
        setupP  = setupProve @(PlonkBS N) @core plonk
        setupV  = setupVerify @(PlonkBS N) @core plonk
        witness = (PlonkupWitnessInput witnessInputs witnessNewVars, ps)
        (input, proof) = prove @(PlonkBS N) @core setupP witness

        -- `one` corresponds to `True`
        circuitOutputsTrue = plonkupVerifierInput $ V.singleton one

    in unPlonkupInput input Haskell.== unPlonkupInput circuitOutputsTrue Haskell.&& verify @(PlonkBS N) @core setupV circuitOutputsTrue proof

testSafeOneInputZKP :: forall core . (CoreFunction C core) => F -> PlonkupProverSecret C -> F -> Haskell.Bool
testSafeOneInputZKP x ps targetValue =
    let Bool ac = compileForceOne @F (lockedByTxId @F @(ArithmeticCircuit F (V.Vector 1)) targetValue) :: Bool (ArithmeticCircuit F (V.Vector 1))

        (omega, k1, k2) = getParams 32
        witnessInputs  = V.singleton targetValue
        witnessNewVars = witnessGenerator ac witnessInputs
        indexTargetValue = V.singleton (InVar zero)
        plonk   = Plonkup @1 @32 omega k1 k2 indexTargetValue ac x
        setupP  = setupProve @(PlonkBS N) @core plonk
        setupV  = setupVerify @(PlonkBS N) @core plonk
        witness = (PlonkupWitnessInput witnessInputs witnessNewVars, ps)
        (input, proof) = prove @(PlonkBS N) @core setupP witness

        onePublicInput = plonkupVerifierInput $ V.singleton targetValue

    in unPlonkupInput input Haskell.== unPlonkupInput onePublicInput Haskell.&& verify @(PlonkBS N) @core setupV onePublicInput proof

testAttackSafeOneInputZKP :: forall core . (CoreFunction C core) => F -> PlonkupProverSecret C -> F -> Haskell.Bool
testAttackSafeOneInputZKP x ps targetValue =
    let Bool ac = compileForceOne @F (lockedByTxId @F @(ArithmeticCircuit F (V.Vector 1)) targetValue) :: Bool (ArithmeticCircuit F (V.Vector 1))

        (omega, k1, k2) = getParams 32
        witnessInputs  = V.singleton (targetValue + 1)
        witnessNewVars = witnessGenerator ac witnessInputs
        indexTargetValue = V.singleton (InVar zero)
        plonk   = Plonkup @1 @32 omega k1 k2 indexTargetValue ac x
        setupP  = setupProve @(PlonkBS N) @core plonk
        setupV  = setupVerify @(PlonkBS N) @core plonk
        witness = (PlonkupWitnessInput witnessInputs witnessNewVars, ps)
        (input, proof) = prove @(PlonkBS N) @core setupP witness

        onePublicInput = plonkupVerifierInput $ V.singleton $ targetValue + 1

    in unPlonkupInput input Haskell.== unPlonkupInput onePublicInput Haskell.&& Haskell.not (verify @(PlonkBS N) @core setupV onePublicInput proof)

specArithmetization4 :: Spec
specArithmetization4 = do
    describe "LockedByTxId arithmetization test 1" $ do
        it "should pass" $ property testSameValue
    describe "LockedByTxId arithmetization test 2" $ do
        it "should pass" $ property $ \x y -> x Haskell./= y ==> testDifferentValue x y
    describe "LockedByTxId ZKP test only output" $ do
        it "should pass" $ withMaxSuccess 10 $ property $ testOnlyOutputZKP @HaskellCore
    describe "LockedByTxId ZKP test safe one public input" $ do
       it "should pass" $ withMaxSuccess 10 $ property $ testSafeOneInputZKP @HaskellCore
    describe "LockedByTxId ZKP test attack safe one public input" $ do
       it "should pass" $ withMaxSuccess 10 $ property $ testAttackSafeOneInputZKP @HaskellCore
