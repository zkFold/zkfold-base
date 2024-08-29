{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.NonInteractiveProof.Plonkup (PlonkBS, specPlonk) where

import           Data.ByteString                                     (ByteString)
import           Data.Functor                                        ((<&>))
import           Data.Functor.Rep                                    (Representable (..))
import           Data.List                                           (transpose)
import qualified Data.Map                                            as Map
import           Data.Maybe                                          (fromJust)
import qualified Data.Vector                                         as V
import           GHC.IsList                                          (IsList (..))
import           Prelude                                             hiding (Fractional (..), Num (..), drop, length,
                                                                      replicate, take)
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class                     (AdditiveGroup (..), AdditiveSemigroup (..),
                                                                      FiniteField, FromConstant (..),
                                                                      MultiplicativeSemigroup (..), Scale (..), negate,
                                                                      zero, (-!))
import           ZkFold.Base.Algebra.Basic.Number                    (KnownNat, value)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381         (BLS12_381_G1, BLS12_381_G2)
import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..))
import           ZkFold.Base.Algebra.Polynomials.Univariate          (evalPolyVec, fromPolyVec, polyVecInLagrangeBasis,
                                                                      polyVecLinear, polyVecZero, toPolyVec)
import           ZkFold.Base.Data.Vector                             (fromVector)
import           ZkFold.Base.Protocol.NonInteractiveProof            (HaskellCore, NonInteractiveProof (..),
                                                                      NonInteractiveProofTestData (..))
import           ZkFold.Base.Protocol.Plonkup
import           ZkFold.Base.Protocol.Plonkup.PlonkConstraint
import           ZkFold.Base.Protocol.Plonkup.Relation               (PlonkupRelation (..), toPlonkRelation)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

type PlonkPolyLengthBS = 32
type PlonkBS n = Plonk 1 PlonkPolyLengthBS n BLS12_381_G1 BLS12_381_G2 ByteString
type PlonkPolyExtendedLengthBS = PlonkPolyExtendedLength PlonkPolyLengthBS

propPlonkConstraintConversion :: (Eq a, Scale a a, FromConstant a a, FiniteField a) => PlonkConstraint 1 a -> Bool
propPlonkConstraintConversion p =
    toPlonkConstraint (fromPlonkConstraint p) == p

propPlonkConstraintSatisfaction :: forall n core . KnownNat n => NonInteractiveProofTestData (PlonkBS n) core -> Bool
propPlonkConstraintSatisfaction (TestData (Plonk _ _ _ iPub ac _) w) =
    let pr   = fromJust $ toPlonkRelation @1 @PlonkPolyLengthBS iPub ac
        (PlonkWitnessInput wInput wNewVars, _) = w
        (w1', w2', w3') = wmap pr wInput wNewVars

        wPub = toPolyVec @_ @PlonkPolyLengthBS $
          fromList (fromVector iPub) <&> negate . \case
            InVar j -> index wInput j
            NewVar j -> wNewVars Map.! j

        qm' = V.toList $ fromPolyVec $ qM pr
        ql' = V.toList $ fromPolyVec $ qL pr
        qr' = V.toList $ fromPolyVec $ qR pr
        qo' = V.toList $ fromPolyVec $ qO pr
        qc' = V.toList $ fromPolyVec $ qC pr

        f [qlX, qrX, qoX, qmX, qcX, w1X, w2X, w3X, wPubX] =
            qlX * w1X + qrX * w2X + qoX * w3X + qmX * w1X * w2X + qcX + wPubX
        f _ = error "impossible"

    in all ((== zero) . f) $ transpose [ql', qr', qo', qm', qc', toList $ fromPolyVec w1', toList $ fromPolyVec w2', toList $ fromPolyVec w3', toList $ fromPolyVec wPub]

propPlonkPolyIdentity :: forall n  core . NonInteractiveProofTestData (PlonkBS n) core -> Bool
propPlonkPolyIdentity (TestData plonk w) =
    let zH = polyVecZero @(ScalarField BLS12_381_G1) @PlonkPolyLengthBS @PlonkPolyExtendedLengthBS

        s = setupProve @(PlonkBS n) @core plonk
        (PlonkSetupParamsProve {..}, _, PlonkCircuitPolynomials {..}, PlonkWitnessMap wmap) = s
        (pw@(PlonkWitnessInput wInput wNewVars), ps) = w
        PlonkProverSecret b1 b2 b3 b4 b5 b6 _ _ _ _ _ _ _ _ _ _ _ _ _ = ps
        (w1, w2, w3) = wmap pw

        wPub = iPub' <&> negate . \case
            InVar j -> index wInput j
            NewVar j -> wNewVars Map.! j

        -- wPub = fmap (negate . index wInput . fromIntegral) iPub'
        pubPoly = polyVecInLagrangeBasis @(ScalarField BLS12_381_G1) @PlonkPolyLengthBS @PlonkPolyExtendedLengthBS omega' $
            toPolyVec @(ScalarField BLS12_381_G1) @PlonkPolyLengthBS wPub

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

    in all ((== zero) . f . (omega'^)) [0 .. value @PlonkPolyLengthBS -! 1]

specPlonk :: IO ()
specPlonk = hspec $ do
    describe "Plonk specification" $ do
        describe "Conversion to Plonk constraints and back" $ do
            it "produces equivalent polynomials" $ property $ propPlonkConstraintConversion @(ScalarField BLS12_381_G1)
        describe "Plonk constraint satisfaction" $ do
            it "should hold" $ property $ propPlonkConstraintSatisfaction @2 @HaskellCore
        describe "Plonk polynomial identity" $ do
            it "should hold" $ property $ propPlonkPolyIdentity @2 @HaskellCore
