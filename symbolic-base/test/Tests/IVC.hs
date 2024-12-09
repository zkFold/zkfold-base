{-# LANGUAGE TypeOperators        #-}

module Tests.IVC (specIVC) where

import           GHC.Generics                                    (Par1 (..), U1 (..), type (:*:) (..), type (:.:) (..))
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
import           ZkFold.Base.Protocol.IVC.FiatShamir             (FiatShamir, fiatShamirTransform)
import           ZkFold.Base.Protocol.IVC.NARK                   (NARKInstanceProof (..), NARKProof (..), narkInstanceProof)
import           ZkFold.Base.Protocol.IVC.Oracle                 (MiMCHash)
import           ZkFold.Base.Protocol.IVC.Predicate              (Predicate (..))
import           ZkFold.Base.Protocol.IVC.SpecialSound           (specialSoundProtocol)
import           ZkFold.Prelude                                  (replicate)
import           ZkFold.Symbolic.Class                           (Symbolic)
import           ZkFold.Symbolic.Compiler                        (ArithmeticCircuit, acSizeN, compileWith, guessOutput, hlmap, hpmap)
import           ZkFold.Symbolic.Data.FieldElement               (FieldElement (..))

type F = Zp BLS12_381_Scalar
type G = Point BLS12_381_G1
type I = Vector 1
type P = U1
type M = [F]
type K = 1
type AC = ArithmeticCircuit F (Vector 1 :*: U1) (Vector 1) U1
type PHI = Predicate F I P
type SPS = FiatShamir F I P [F] [F] G D 1
type D = 2
type PARDEG = 5
type PAR = PolyVec F PARDEG

testFunction :: forall ctx . (Symbolic ctx, FromConstant F (FieldElement ctx))
    => PAR -> Vector 1 (FieldElement ctx) -> Vector 1 (FieldElement ctx)
testFunction p x =
    let p' = fromList $ map fromConstant $ toList p :: PolyVec (FieldElement ctx) PARDEG
    in singleton $ evalPolyVec p' $ item x

testFunction' :: PAR -> Vector 1 F -> Vector 1 F
testFunction' p x =
    let p' = fromList $ toList p :: PolyVec F PARDEG
    in singleton $ evalPolyVec p' $ item x

testCircuit :: PAR -> AC
testCircuit p =
    hpmap (\(x :*: U1) -> Comp1 (Par1 <$> x) :*: U1) $
    hlmap (\x -> U1 :*: Comp1 (Par1 <$> x)) $
    compileWith @F guessOutput (\x U1 -> (Comp1 (singleton U1) :*: U1, x)) $ testFunction p

testPredicate :: PAR -> PHI
testPredicate p = Predicate (\x _ -> testFunction' p x) (testCircuit p)

testSPS :: PAR -> SPS
testSPS = fiatShamirTransform @MiMCHash . commitOpen . specialSoundProtocol . testPredicate

initAccumulator :: PHI -> Accumulator I M G K F
initAccumulator = emptyAccumulator @D

initAccumulatorInstance :: PHI -> AccumulatorInstance I G K F
initAccumulatorInstance sps =
    let Accumulator ai _ = initAccumulator sps
    in ai

testPublicInput0 :: I F
testPublicInput0 = singleton $ fromConstant @Natural 42

testInstanceProofPair :: SPS -> NARKInstanceProof F I M G K
testInstanceProofPair sps = narkInstanceProof sps testPublicInput0 U1

testMessages :: SPS -> Vector K M
testMessages sps =
    let NARKInstanceProof _ (NARKProof _ ms) = testInstanceProofPair sps
    in ms

testNarkProof :: SPS -> Vector K G
testNarkProof sps =
    let NARKInstanceProof _ (NARKProof cs _) = testInstanceProofPair sps
    in cs

testPublicInput :: SPS -> I F
testPublicInput sps =
    let NARKInstanceProof pi _ = testInstanceProofPair sps
    in pi

testAccumulatorScheme :: PHI -> AccumulatorScheme F I [F] [F] G D 1
testAccumulatorScheme = accumulatorScheme @MiMCHash

testAccumulator :: SPS -> PHI -> Accumulator I M G K F
testAccumulator sps phi = 
    let s = testAccumulatorScheme phi
    in fst $ prover s (initAccumulator phi) $ testInstanceProofPair sps

testAccumulatorInstance :: SPS -> PHI -> AccumulatorInstance I G K F
testAccumulatorInstance sps phi =
    let Accumulator ai _ = testAccumulator sps phi
    in ai

testAccumulationProof :: SPS -> PHI -> Vector (D - 1) G
testAccumulationProof sps phi =
    let s = testAccumulatorScheme phi
    in snd $ prover s (initAccumulator phi) $ testInstanceProofPair sps

testDeciderResult :: SPS -> PHI -> (Vector K G, G)
testDeciderResult sps phi =
    let s = testAccumulatorScheme phi
    in decider s $ testAccumulator sps phi

testVerifierResult :: SPS -> PHI -> (F, I F, Vector (K-1) F, Vector K G, G)
testVerifierResult sps phi = 
    let s = testAccumulatorScheme phi
    in verifier s (testPublicInput sps) (testNarkProof sps) (initAccumulatorInstance phi) (testAccumulatorInstance sps phi) (testAccumulationProof sps phi)

specAlgebraicMap :: IO ()
specAlgebraicMap = hspec $ do
    describe "Algebraic map specification" $ do
        describe "Algebraic map" $ do
            it "must output zeros on the public input and testMessages" $ do
               withMaxSuccess 10 $ property $
                    \p -> algebraicMap @D (testPredicate p) (testPublicInput $ testSPS p) (testMessages $ testSPS p) (unsafeToVector []) one
                        == replicate (acSizeN $ testCircuit p) zero

specAccumulatorScheme :: IO ()
specAccumulatorScheme = hspec $ do
    describe "Accumulator scheme specification" $ do
        describe "decider" $ do
            it  "must output zeros" $ do
                withMaxSuccess 10 $ property $ \p -> testDeciderResult (testSPS p) (testPredicate p) == (singleton zero, zero)
        describe "verifier" $ do
            it "must output zeros" $ do
                withMaxSuccess 10 $ property $ \p -> testVerifierResult (testSPS p) (testPredicate p)
                    == (zero, singleton zero, unsafeToVector [], singleton zero, zero)

specIVC :: IO ()
specIVC = do
    p <- generate arbitrary :: IO (PolyVec F PARDEG)
    print $ "Recursion circuit size: " ++ show (acSizeN $ testCircuit p)
    specAlgebraicMap
    specAccumulatorScheme
