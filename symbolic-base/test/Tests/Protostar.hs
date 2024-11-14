{-# LANGUAGE TypeOperators #-}

module Tests.Protostar (specProtostar) where

import           GHC.Generics                                     (Par1 (..), U1 (..), type (:*:) (..), type (:.:) (..))
import           GHC.IsList                                       (IsList (..))
import           Prelude                                          hiding (Num (..), replicate, sum, (+))
import           Test.Hspec                                       (describe, hspec, it)
import           Test.QuickCheck                                  (property, withMaxSuccess)

import           ZkFold.Base.Algebra.Basic.Class                  (FromConstant (..), one, zero)
import           ZkFold.Base.Algebra.Basic.Field                  (Zp)
import           ZkFold.Base.Algebra.Basic.Number                 (Natural, type(-))
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381      (BLS12_381_G1, BLS12_381_Scalar)
import           ZkFold.Base.Algebra.EllipticCurve.Class          (Point)
import           ZkFold.Base.Algebra.Polynomials.Univariate       (PolyVec, evalPolyVec)
import           ZkFold.Base.Data.HFunctor                        (hmap)
import           ZkFold.Base.Data.Vector                          (Vector, item, singleton, unsafeToVector)
import           ZkFold.Base.Protocol.Protostar.Accumulator       (Accumulator (..), AccumulatorInstance (..))
import           ZkFold.Base.Protocol.Protostar.AccumulatorScheme as Acc
import           ZkFold.Base.Protocol.Protostar.AlgebraicMap      (AlgebraicMap (..))
import           ZkFold.Base.Protocol.Protostar.CommitOpen        (CommitOpen (..))
import           ZkFold.Base.Protocol.Protostar.FiatShamir        (FiatShamir (..))
import           ZkFold.Base.Protocol.Protostar.NARK              (InstanceProofPair (..), NARKProof (..),
                                                                   instanceProof)
import           ZkFold.Prelude                                   (replicate)
import           ZkFold.Symbolic.Class                            (Symbolic)
import           ZkFold.Symbolic.Compiler                         (ArithmeticCircuit, acSizeM, acSizeN, compile, hlmap)
import           ZkFold.Symbolic.Data.FieldElement                (FieldElement (..))

type F = Zp BLS12_381_Scalar
type G = Point BLS12_381_G1
type PI = Vector 1 F
type M = [F]
type K = 1
type AC = ArithmeticCircuit F (Vector 1) (Vector 1)
type SPS = FiatShamir F (CommitOpen M G AC)
type D = Degree AC
type PARDEG = 5
type PAR = PolyVec F PARDEG

testFunction :: forall ctx . (Symbolic ctx, FromConstant F (FieldElement ctx))
    => PAR -> Vector 1 (FieldElement ctx) -> Vector 1 (FieldElement ctx)
testFunction p x =
    let p' = fromList $ map fromConstant $ toList p :: PolyVec (FieldElement ctx) PARDEG
    in singleton $ evalPolyVec p' $ item x

testCircuit :: PAR -> AC
testCircuit p =
    hlmap (\x -> Comp1 (Par1 <$> x) :*: U1)
    $ hmap (\(Comp1 x') -> unPar1 <$> x')
    $ compile @F $ testFunction p

testSPS :: PAR -> SPS
testSPS = FiatShamir . CommitOpen . testCircuit

testMessageLength :: SPS -> Natural
testMessageLength (FiatShamir (CommitOpen ac)) = acSizeM ac

initAccumulator :: SPS -> Accumulator PI F G M K
initAccumulator sps = Accumulator (AccumulatorInstance (singleton zero) (singleton zero) (unsafeToVector []) zero zero) (singleton $ replicate (testMessageLength sps) zero)

initAccumulatorInstance :: SPS -> AccumulatorInstance PI F G K
initAccumulatorInstance sps =
    let Accumulator ai _ = initAccumulator sps
    in ai

testPublicInput :: PI
testPublicInput = singleton $ fromConstant @Natural 42

testInstanceProofPair :: SPS -> InstanceProofPair PI G M K
testInstanceProofPair sps = instanceProof @_ @F sps testPublicInput

testMessages :: SPS -> Vector K M
testMessages sps =
    let InstanceProofPair _ (NARKProof _ ms) = testInstanceProofPair sps
    in ms

testNarkProof :: SPS -> Vector K G
testNarkProof sps =
    let InstanceProofPair _ (NARKProof cs _) = testInstanceProofPair sps
    in cs

testAccumulator :: SPS -> Accumulator PI F G M K
testAccumulator sps = fst $ Acc.prover  @PI @F @G @M @K @D sps (initAccumulator sps) $ testInstanceProofPair sps

testAccumulatorInstance :: SPS -> AccumulatorInstance PI F G K
testAccumulatorInstance sps =
    let Accumulator ai _ = testAccumulator sps
    in ai

testAccumulationProof :: SPS -> Vector (D - 1) G
testAccumulationProof sps = snd $ Acc.prover sps (initAccumulator sps) $ testInstanceProofPair sps

testDeciderResult :: SPS -> (Vector K G, G)
testDeciderResult sps = decider  @PI @F @G @M @K @D sps $ testAccumulator sps

testVerifierResult :: SPS -> (F, PI, Vector (K-1) F, Vector K G, G)
testVerifierResult sps = Acc.verifier @PI @F @G @M @K @D @(FiatShamir F (CommitOpen M G AC))
    testPublicInput (testNarkProof sps) (initAccumulatorInstance sps) (testAccumulatorInstance sps) (testAccumulationProof sps)

specAlgebraicMap :: IO ()
specAlgebraicMap = hspec $ do
    describe "Algebraic map specification" $ do
        describe "Algebraic map" $ do
            it "must output zeros on the public input and testMessages" $ do
                withMaxSuccess 10 $ property $
                    \x0 -> algebraicMap (testCircuit x0) testPublicInput (testMessages $ testSPS x0) (unsafeToVector []) one == replicate (acSizeN $ testCircuit x0) zero

specAccumulatorScheme :: IO ()
specAccumulatorScheme = hspec $ do
    describe "Accumulator scheme specification" $ do
        describe "decider" $ do
            it  "must output zeros" $ do
                withMaxSuccess 10 $ property $ \x0 -> testDeciderResult (testSPS x0) == (singleton zero, zero)
        describe "verifier" $ do
            it "must output zeros" $ do
                withMaxSuccess 10 $ property $ \x0 -> testVerifierResult (testSPS x0) == (zero, singleton zero, unsafeToVector [], singleton zero, zero)

specProtostar :: IO ()
specProtostar = do
    specAlgebraicMap
    specAccumulatorScheme
