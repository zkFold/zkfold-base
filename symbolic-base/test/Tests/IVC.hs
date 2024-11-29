{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Tests.IVC (specIVC) where

import           GHC.Generics                                    (Par1 (..), U1 (..), type (:*:) (..), type (:.:) (..))
import           GHC.IsList                                      (IsList (..))
import           Prelude                                         hiding (Num (..), pi, replicate, sum, (+))
import           Test.Hspec                                      (describe, hspec, it)
import           Test.QuickCheck                                 (property, withMaxSuccess)

import           ZkFold.Base.Algebra.Basic.Class                 (FromConstant (..), one, zero)
import           ZkFold.Base.Algebra.Basic.Field                 (Zp)
import           ZkFold.Base.Algebra.Basic.Number                (Natural, type (-))
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381     (BLS12_381_G1, BLS12_381_Scalar)
import           ZkFold.Base.Algebra.EllipticCurve.Class         (Point)
import           ZkFold.Base.Algebra.Polynomials.Univariate      (PolyVec, evalPolyVec)
import           ZkFold.Base.Data.Vector                         (Vector (..), item, singleton, unsafeToVector)
import           ZkFold.Base.Protocol.IVC.Accumulator            (Accumulator (..), AccumulatorInstance (..), emptyAccumulator)
import           ZkFold.Base.Protocol.IVC.AccumulatorScheme      as Acc
import           ZkFold.Base.Protocol.IVC.AlgebraicMap           (AlgebraicMap (..))
import           ZkFold.Base.Protocol.IVC.ArithmetizableFunction (ArithmetizableFunction (..))
import           ZkFold.Base.Protocol.IVC.CommitOpen             (CommitOpen (..))
import           ZkFold.Base.Protocol.IVC.FiatShamir             (FiatShamir (..))
import           ZkFold.Base.Protocol.IVC.NARK                   (NARKInstanceProof (..), NARKProof (..), narkInstanceProof)
import           ZkFold.Base.Protocol.IVC.Oracle                 (MiMCHash)
import           ZkFold.Prelude                                  (replicate)
import           ZkFold.Symbolic.Class                           (Symbolic)
import           ZkFold.Symbolic.Compiler                        (ArithmeticCircuit, acSizeN, compileWith, guessOutput, hlmap, hpmap)
import           ZkFold.Symbolic.Data.FieldElement               (FieldElement (..))

type F = Zp BLS12_381_Scalar
type G = Point BLS12_381_G1
type I = Vector 1
type M = [F]
type K = 1
type AC = ArithmeticCircuit F (Vector 1 :*: U1) (Vector 1) U1
type AF = ArithmetizableFunction F I U1
type SPS = FiatShamir MiMCHash (CommitOpen AF)
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

testArithmetizableFunction :: PAR -> ArithmetizableFunction F I U1
testArithmetizableFunction p = ArithmetizableFunction (\x _ -> testFunction' p x) (testCircuit p)

testSPS :: PAR -> SPS
testSPS = FiatShamir . CommitOpen . testArithmetizableFunction

initAccumulator :: SPS -> Accumulator F I M G K
initAccumulator = emptyAccumulator @_ @_ @_ @_ @D

initAccumulatorInstance :: SPS -> AccumulatorInstance F I G K
initAccumulatorInstance sps =
    let Accumulator ai _ = initAccumulator sps
    in ai

testPublicInput0 :: I F
testPublicInput0 = singleton $ fromConstant @Natural 42

testInstanceProofPair :: SPS -> NARKInstanceProof F I M G K
testInstanceProofPair sps = narkInstanceProof @_ @_ @_ @_ @_ @D sps testPublicInput0 U1

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

testAccumulator :: SPS -> Accumulator F I M G K
testAccumulator sps = fst $ Acc.prover @F @I @M @G @D @K sps (initAccumulator sps) $ testInstanceProofPair sps

testAccumulatorInstance :: SPS -> AccumulatorInstance F I G K
testAccumulatorInstance sps =
    let Accumulator ai _ = testAccumulator sps
    in ai

testAccumulationProof :: SPS -> Vector (D - 1) G
testAccumulationProof sps = snd $ Acc.prover sps (initAccumulator sps) $ testInstanceProofPair sps

testDeciderResult :: SPS -> (Vector K G, G)
testDeciderResult sps = decider @F @I @M @G @D @K sps $ testAccumulator sps

testVerifierResult :: SPS -> (F, I F, Vector (K-1) F, Vector K G, G)
testVerifierResult sps = Acc.verifier @F @I @M @G @D @K @SPS
    (testPublicInput sps) (testNarkProof sps) (initAccumulatorInstance sps) (testAccumulatorInstance sps) (testAccumulationProof sps)

specAlgebraicMap :: IO ()
specAlgebraicMap = hspec $ do
    describe "Algebraic map specification" $ do
        describe "Algebraic map" $ do
            it "must output zeros on the public input and testMessages" $ do
                property $
                    \p -> algebraicMap @_ @_ @D (testArithmetizableFunction p) (testPublicInput $ testSPS p) (testMessages $ testSPS p) (unsafeToVector []) one
                        == replicate (acSizeN $ testCircuit p) zero

specAccumulatorScheme :: IO ()
specAccumulatorScheme = hspec $ do
    describe "Accumulator scheme specification" $ do
        describe "decider" $ do
            it  "must output zeros" $ do
                withMaxSuccess 10 $ property $ \p -> testDeciderResult (testSPS p) == (singleton zero, zero)
        describe "verifier" $ do
            it "must output zeros" $ do
                withMaxSuccess 10 $ property $ \p -> testVerifierResult (testSPS p) == (zero, singleton zero, unsafeToVector [], singleton zero, zero)

specIVC :: IO ()
specIVC = do
    specAlgebraicMap
    specAccumulatorScheme
