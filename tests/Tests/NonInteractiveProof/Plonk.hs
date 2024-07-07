{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.NonInteractiveProof.Plonk (PlonkBS, PlonkMaxPolyDegreeBS, PlonkSizeBS, specPlonk) where

import           Data.ByteString                            (ByteString)
import           Data.List                                  (sort, transpose)
import           Data.Maybe                                 (fromJust)
import qualified Data.Vector                                as V
import           GHC.IsList                                 (IsList (..))
import           Prelude                                    hiding (Fractional (..), Num (..), drop, length, replicate,
                                                             take)
import           Test.Hspec
import           Test.QuickCheck
import           Tests.NonInteractiveProof.Internal         (NonInteractiveProofTestData (..))

import           ZkFold.Base.Algebra.Basic.Class            (AdditiveGroup (..), AdditiveSemigroup (..), FiniteField,
                                                             MultiplicativeSemigroup (..), negate, zero, (-!))
import           ZkFold.Base.Algebra.Basic.Number           (KnownNat, value)
import           ZkFold.Base.Algebra.Polynomials.Univariate (evalPolyVec, fromPolyVec, polyVecInLagrangeBasis,
                                                             polyVecLinear, polyVecZero, toPolyVec)
import           ZkFold.Base.Protocol.ARK.Plonk
import           ZkFold.Base.Protocol.ARK.Plonk.Constraint
import           ZkFold.Base.Protocol.ARK.Plonk.Relation    (PlonkRelation (..), toPlonkRelation)
import           ZkFold.Base.Protocol.NonInteractiveProof   (NonInteractiveProof (..))
import           ZkFold.Prelude                             (replicate, take)

type PlonkSizeBS = 32
type PlonkBS n = Plonk PlonkSizeBS n ByteString
type PlonkMaxPolyDegreeBS = PlonkMaxPolyDegree PlonkSizeBS

propPlonkConstraintConversion :: (Eq a, FiniteField a) => PlonkConstraint a -> Bool
propPlonkConstraintConversion p =
    toPlonkConstraint (fromPlonkConstraint p) == p

propPlonkConstraintSatisfaction :: forall n . KnownNat n => PlonkBS n -> NonInteractiveProofTestData (PlonkBS n) -> Bool
propPlonkConstraintSatisfaction (Plonk _ _ _ iPub ac _) (TestData _ w) =
    let pr   = fromJust $ toPlonkRelation @PlonkSizeBS iPub ac
        (PlonkWitnessInput wInput, _) = w
        (w1', w2', w3') = wmap pr wInput

        input = take (value @n) $ fmap (negate . snd) (sort $ toList wInput)
        wPub  = input ++ replicate (value @PlonkSizeBS -! (value @n)) zero

        qm' = V.toList $ fromPolyVec $ qM pr
        ql' = V.toList $ fromPolyVec $ qL pr
        qr' = V.toList $ fromPolyVec $ qR pr
        qo' = V.toList $ fromPolyVec $ qO pr
        qc' = V.toList $ fromPolyVec $ qC pr

        f [qlX, qrX, qoX, qmX, qcX, w1X, w2X, w3X, wPubX] =
            qlX * w1X + qrX * w2X + qoX * w3X + qmX * w1X * w2X + qcX + wPubX
        f _ = error "impossible"

    in all ((== zero) . f) $ transpose [ql', qr', qo', qm', qc', toList $ fromPolyVec w1', toList $ fromPolyVec w2', toList $ fromPolyVec w3', wPub]

propPlonkPolyIdentity :: forall n . KnownNat n => NonInteractiveProofTestData (PlonkBS n) -> Bool
propPlonkPolyIdentity (TestData plonk w) =
    let zH = polyVecZero @F @PlonkSizeBS @PlonkMaxPolyDegreeBS

        s = setupProve @(PlonkBS n) plonk
        (PlonkSetupParamsProve {..}, _, PlonkCircuitPolynomials {..}, PlonkWitnessMap wmap) = s
        (PlonkWitnessInput wInput, ps) = w
        PlonkProverSecret b1 b2 b3 b4 b5 b6 _ _ _ _ _ = ps
        (w1, w2, w3) = wmap wInput

        input   = V.fromList $ take 2 $ fmap (negate . snd) (sort $ toList wInput)
        pubPoly = polyVecInLagrangeBasis @F @PlonkSizeBS @PlonkMaxPolyDegreeBS omega' $ toPolyVec @F @PlonkSizeBS input

        a = polyVecLinear b2 b1 * zH + polyVecInLagrangeBasis omega' w1
        b = polyVecLinear b4 b3 * zH + polyVecInLagrangeBasis omega' w2
        c = polyVecLinear b6 b5 * zH + polyVecInLagrangeBasis omega' w3

        f x =
            let qlX = ql `evalPolyVec` x
                qrX = qr `evalPolyVec` x
                qoX = qo `evalPolyVec` x
                qmX = qm `evalPolyVec` x
                qcX = qc `evalPolyVec` x
                aX = a `evalPolyVec` x
                bX = b `evalPolyVec` x
                cX = c `evalPolyVec` x
                pubX = pubPoly `evalPolyVec` x
            in qlX * aX + qrX * bX + qoX * cX + qmX * aX * bX + qcX + pubX

    in all ((== zero) . f . (omega'^)) [0 .. value @PlonkSizeBS -! 1]

specPlonk :: IO ()
specPlonk = hspec $ do
    describe "Plonk specification" $ do
        describe "Conversion to Plonk constraints and back" $ do
            it "produces equivalent polynomials" $ property $ propPlonkConstraintConversion @F
        describe "Plonk constraint satisfaction" $ do
            it "should hold" $ property $ propPlonkConstraintSatisfaction @1
        describe "Plonk polynomial identity" $ do
            it "should hold" $ property $ propPlonkPolyIdentity @1
