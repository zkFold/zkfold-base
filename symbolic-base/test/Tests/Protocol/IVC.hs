{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module Tests.Protocol.IVC (specIVC) where

import           GHC.Generics                               (Par1, U1 (..), type (:.:) (..))
import           GHC.IsList                                 (IsList (..))
import           Prelude                                    hiding (Bool (..), Num (..), pi, replicate, sum, (+))
import           Test.Hspec                                 (Spec, describe, it, runIO)
import           Test.QuickCheck                            (arbitrary, generate, property, withMaxSuccess)
import           Tests.Algebra.Group                        (specAdditiveGroup')
import           Tests.Protocol.IVC.CycleFold               (specCycleFold)
import           Tests.Protocol.IVC.Types

import           ZkFold.Base.Algebra.Basic.Class            (FromConstant (..), Ring, ToConstant (..), one, zero)
import           ZkFold.Base.Algebra.Basic.Number           (Natural, type (-))
import           ZkFold.Base.Algebra.Polynomials.Univariate (PolyVec, evalPolyVec)
import           ZkFold.Base.Data.Vector                    (Vector (..), item, singleton, unsafeToVector)
import           ZkFold.Base.Protocol.IVC                   (ivc)
import           ZkFold.Base.Protocol.IVC.Accumulator       (Accumulator (..), AccumulatorInstance (..),
                                                             emptyAccumulator, emptyAccumulatorInstance)
import           ZkFold.Base.Protocol.IVC.AccumulatorScheme as Acc
import           ZkFold.Base.Protocol.IVC.AlgebraicMap      (AlgebraicMap, algebraicMap)
import           ZkFold.Base.Protocol.IVC.Commit            ()
import           ZkFold.Base.Protocol.IVC.CommitOpen        (commitOpen)
import           ZkFold.Base.Protocol.IVC.CycleFold         (ForeignPoint)
import           ZkFold.Base.Protocol.IVC.FiatShamir        (fiatShamir)
import           ZkFold.Base.Protocol.IVC.NARK              (NARKInstanceProof (..), NARKProof (..), narkInstanceProof)
import           ZkFold.Base.Protocol.IVC.Oracle            (MiMCHash)
import           ZkFold.Base.Protocol.IVC.Predicate         (Predicate (..), predicate)
import           ZkFold.Base.Protocol.IVC.RecursiveFunction (RecursiveI (..), RecursiveP, recursiveFunction)
import           ZkFold.Base.Protocol.IVC.SpecialSound      (specialSoundProtocol)
import           ZkFold.Prelude                             (replicate)
import           ZkFold.Symbolic.Compiler                   (acSizeN)
import           ZkFold.Symbolic.Data.Bool                  (Bool, true)
import           ZkFold.Symbolic.Data.Payloaded             (Payloaded (..))
import           ZkFold.Symbolic.Interpreter                (Interpreter)

testFunction :: forall f . (Ring f)
    => PAR -> Vector 1 f -> U1 f -> Vector 1 f
testFunction p x _ =
    let p' = fromList $ map (fromConstant . toConstant) $ toList p :: PolyVec f PARDEG
    in singleton $ evalPolyVec p' $ item x

testPredicate :: PAR -> PHI
testPredicate p = predicate $ testFunction p

testRecursivePredicate :: PAR -> Predicate A (RecursiveI I) (RecursiveP D K I P Par1)
testRecursivePredicate p = predicate $ recursiveFunction @MiMCHash @A (testFunction p)

testPredicateCircuit :: PAR -> AC
testPredicateCircuit p = predicateCircuit @A @I @P $ testPredicate p

testAlgebraicMap :: PHI -> AlgebraicMap K I W
testAlgebraicMap = algebraicMap @D

testSPS :: PHI -> SPS
testSPS = fiatShamir @MiMCHash @K @A @I @P @C . commitOpen @K @A @I @P @C  . specialSoundProtocol @D @A @I @P

testPublicInput0 :: I W
testPublicInput0 = singleton $ fromConstant @Natural 42

testPublicInput :: PHI -> I W
testPublicInput phi = predicateFunction phi testPublicInput0 U1

testInstanceProofPair :: PHI -> NARKInstanceProof K I C W
testInstanceProofPair phi = narkInstanceProof (testSPS phi) testPublicInput0 U1

testMessages :: PHI -> Vector K [W]
testMessages phi =
    let NARKInstanceProof _ (NARKProof _ ms) = testInstanceProofPair phi
    in ms

testNarkProof :: PHI -> Vector K (C W)
testNarkProof phi =
    let NARKInstanceProof _ (NARKProof cs _) = testInstanceProofPair phi
    in cs

testAccumulatorScheme :: PHI -> AccumulatorScheme D K A I C
testAccumulatorScheme = accumulatorScheme @MiMCHash

testAccumulator :: PHI -> Accumulator K I C W
testAccumulator phi =
    let s = testAccumulatorScheme phi
    in fst $ prover s emptyAccumulator $ testInstanceProofPair phi

testAccumulatorInstance :: PHI -> AccumulatorInstance K I C W
testAccumulatorInstance phi =
    let Accumulator ai _ = testAccumulator phi
    in ai

testAccumulationProof :: PHI -> Vector (D - 1) (C W)
testAccumulationProof phi =
    let s = testAccumulatorScheme phi
    in snd $ prover s emptyAccumulator $ testInstanceProofPair phi

testDeciderResult :: PHI -> C F
    -- -> (Vector K (C F), C F)
testDeciderResult phi =
    let s = testAccumulatorScheme phi
    in decider' s $ fromWitness $ testAccumulator phi

testVerifierResult :: PHI -> AccumulatorInstance K I C F
testVerifierResult phi =
    let s = testAccumulatorScheme phi
    in verifier s (fromWitness $ testPublicInput phi) (fromWitness <$> testNarkProof phi) emptyAccumulatorInstance (fromWitness <$> testAccumulationProof phi)

testIVC :: PAR -> Bool CTX
testIVC p = fst $ ivc @MiMCHash @A @D (testFunction p) (Payloaded $ singleton 42) (Payloaded $ Comp1 $ singleton U1)

specAlgebraicMap :: Spec
specAlgebraicMap = do
    describe "Algebraic map specification" $ do
        describe "Algebraic map" $ do
            it "must output zeros on the public input and testMessages" $ do
               withMaxSuccess 10 $ property $
                    \p -> testAlgebraicMap (testPredicate p) (testPublicInput $ testPredicate p) (testMessages $ testPredicate p) (unsafeToVector []) one
                            == replicate (acSizeN $ testPredicateCircuit p) zero

-- TODO
specAccumulatorScheme :: Spec
specAccumulatorScheme = do
    describe "Accumulator scheme specification" $ do
        describe "decider" $ do
            it  "must output zeros" $ do
                withMaxSuccess 10 $ property $ \p -> testDeciderResult (testPredicate p) == zero
                    --(singleton zero, zero)
        describe "verifier" $ do
            it "must output zeros" $ do
                withMaxSuccess 10 $ property $ \p -> testVerifierResult (testPredicate p) == fromWitness (testAccumulatorInstance (testPredicate p))

specIVC' :: Spec
specIVC' = do
    describe "IVC specification" $ do
        describe "IVC (Interpreter)" $ do
            it "must output True" $ do
                withMaxSuccess 10 $ property $ \p -> testIVC p == true

specIVC :: Spec
specIVC = do
    p <- runIO $ generate arbitrary
    runIO $ print $ testPublicInput $ testPredicate p
    runIO $ print $ "Predicate circuit size: " ++ show (acSizeN $ testPredicateCircuit p)
    runIO $ print $ "Recursive circuit size: " ++ show (acSizeN $ predicateCircuit $ testRecursivePredicate p)
    runIO $ print $ testDeciderResult $ testPredicate p
    specCycleFold
    specAlgebraicMap
    specAccumulatorScheme
    specAdditiveGroup' @(ForeignPoint MiMCHash 2 1 A (Interpreter A))
    specIVC'
