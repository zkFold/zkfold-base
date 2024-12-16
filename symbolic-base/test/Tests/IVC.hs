{-# LANGUAGE TypeOperators        #-}

module Tests.IVC (specIVC) where

import           Data.Functor.Constant                           (Constant)
import           GHC.Generics                                    (U1 (..), type (:*:) (..))
import           GHC.IsList                                      (IsList (..))
import           Prelude                                         hiding (Num (..), pi, replicate, sum, (+))
import           Test.Hspec                                      (describe, hspec, it)
import           Test.QuickCheck                                 (property, withMaxSuccess, generate, arbitrary)

import           ZkFold.Base.Algebra.Basic.Class                 (FromConstant (..), one, zero)
import           ZkFold.Base.Algebra.Basic.Field                 (Zp)
import           ZkFold.Base.Algebra.Basic.Number                (Natural, type (-))
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381     (BLS12_381_G1, BLS12_381_Scalar)
import           ZkFold.Base.Algebra.EllipticCurve.Class         (Point)
import           ZkFold.Base.Algebra.Polynomials.Univariate      (PolyVec, evalPolyVec)
import           ZkFold.Base.Data.Vector                         (Vector (..), item, singleton, unsafeToVector)
import           ZkFold.Base.Protocol.IVC.Accumulator            (Accumulator (..), AccumulatorInstance (..), emptyAccumulator)
import           ZkFold.Base.Protocol.IVC.AccumulatorScheme      as Acc
import           ZkFold.Base.Protocol.IVC.AlgebraicMap           (algebraicMap)
import           ZkFold.Base.Protocol.IVC.CommitOpen             (commitOpen)
import           ZkFold.Base.Protocol.IVC.FiatShamir             (FiatShamir, fiatShamir)
import           ZkFold.Base.Protocol.IVC.NARK                   (NARKInstanceProof (..), NARKProof (..), narkInstanceProof)
import           ZkFold.Base.Protocol.IVC.Oracle                 (MiMCHash)
import           ZkFold.Base.Protocol.IVC.Predicate              (Predicate (..), predicate)
import           ZkFold.Base.Protocol.IVC.SpecialSound           (specialSoundProtocol)
import           ZkFold.Prelude                                  (replicate)
import           ZkFold.Symbolic.Class                           (Symbolic, BaseField)
import           ZkFold.Symbolic.Compiler                        (ArithmeticCircuit, acSizeN)
import           ZkFold.Symbolic.Data.FieldElement               (FieldElement (..))

type F = Zp BLS12_381_Scalar
type C = Constant (Point BLS12_381_G1)
type I = Vector 1
type P = U1
type M = [F]
type K = 1
type AC = ArithmeticCircuit F (Vector 1 :*: U1) (Vector 1) U1
type PHI = Predicate F I P
type SPS = FiatShamir 1 I P C [F] [F] F
type D = 2
type PARDEG = 5
type PAR = PolyVec F PARDEG

testFunction :: forall ctx . (Symbolic ctx, FromConstant F (BaseField ctx))
    => PAR -> Vector 1 (FieldElement ctx) -> U1 (FieldElement ctx) -> Vector 1 (FieldElement ctx)
testFunction p x _ =
    let p' = fromList $ map fromConstant $ toList p :: PolyVec (FieldElement ctx) PARDEG
    in singleton $ evalPolyVec p' $ item x

testPredicateCircuit :: PAR -> AC
testPredicateCircuit p = predicateCircuit @F @I @P $ testPredicate p

testPredicate :: PAR -> PHI
testPredicate p = predicate $ testFunction p

testSPS :: PAR -> SPS
testSPS = fiatShamir @MiMCHash . commitOpen . specialSoundProtocol @D . testPredicate

initAccumulator :: PHI -> Accumulator K I C M F
initAccumulator = emptyAccumulator @D

initAccumulatorInstance :: PHI -> AccumulatorInstance K I C F
initAccumulatorInstance sps =
    let Accumulator ai _ = initAccumulator sps
    in ai

testPublicInput0 :: I F
testPublicInput0 = singleton $ fromConstant @Natural 42

testInstanceProofPair :: SPS -> NARKInstanceProof K I C M F
testInstanceProofPair sps = narkInstanceProof sps testPublicInput0 U1

testMessages :: SPS -> Vector K M
testMessages sps =
    let NARKInstanceProof _ (NARKProof _ ms) = testInstanceProofPair sps
    in ms

testNarkProof :: SPS -> Vector K (C F)
testNarkProof sps =
    let NARKInstanceProof _ (NARKProof cs _) = testInstanceProofPair sps
    in cs

testPublicInput :: SPS -> I F
testPublicInput sps =
    let NARKInstanceProof pi _ = testInstanceProofPair sps
    in pi

testAccumulatorScheme :: PHI -> AccumulatorScheme D 1 I C [F] F
testAccumulatorScheme = accumulatorScheme @MiMCHash

testAccumulator :: SPS -> PHI -> Accumulator K I C M F
testAccumulator sps phi =
    let s = testAccumulatorScheme phi
    in fst $ prover s (initAccumulator phi) $ testInstanceProofPair sps

testAccumulatorInstance :: SPS -> PHI -> AccumulatorInstance K I C F
testAccumulatorInstance sps phi =
    let Accumulator ai _ = testAccumulator sps phi
    in ai

testAccumulationProof :: SPS -> PHI -> Vector (D - 1) (C F)
testAccumulationProof sps phi =
    let s = testAccumulatorScheme phi
    in snd $ prover s (initAccumulator phi) $ testInstanceProofPair sps

testDeciderResult :: SPS -> PHI -> (Vector K (C F), C F)
testDeciderResult sps phi =
    let s = testAccumulatorScheme phi
    in decider s $ testAccumulator sps phi

testVerifierResult :: SPS -> PHI -> AccumulatorInstance K I C F
testVerifierResult sps phi =
    let s = testAccumulatorScheme phi
    in verifier s (testPublicInput sps) (testNarkProof sps) (initAccumulatorInstance phi) (testAccumulationProof sps phi)

specAlgebraicMap :: IO ()
specAlgebraicMap = hspec $ do
    describe "Algebraic map specification" $ do
        describe "Algebraic map" $ do
            it "must output zeros on the public input and testMessages" $ do
               withMaxSuccess 10 $ property $
                    \p -> algebraicMap @D (testPredicate p) (testPublicInput $ testSPS p) (testMessages $ testSPS p) (unsafeToVector []) one
                        == replicate (acSizeN $ testPredicateCircuit p) zero

specAccumulatorScheme :: IO ()
specAccumulatorScheme = hspec $ do
    describe "Accumulator scheme specification" $ do
        describe "decider" $ do
            it  "must output zeros" $ do
                withMaxSuccess 10 $ property $ \p -> testDeciderResult (testSPS p) (testPredicate p) == (singleton zero, zero)
        describe "verifier" $ do
            it "must output zeros" $ do
                withMaxSuccess 10 $ property $ \p -> testVerifierResult (testSPS p) (testPredicate p)
                    == testAccumulatorInstance (testSPS p) (testPredicate p)

specIVC :: IO ()
specIVC = do
    p <- generate arbitrary :: IO PAR
    print $ "Recursion circuit size: " ++ show (acSizeN $ testPredicateCircuit p)
    specAlgebraicMap
    specAccumulatorScheme
