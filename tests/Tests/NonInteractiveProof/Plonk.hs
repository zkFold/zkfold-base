{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.NonInteractiveProof.Plonk (PlonkBS, PlonkMaxPolyDegreeBS, PlonkSizeBS, specPlonk) where

import           Data.ByteString                              (ByteString)
import           Data.List                                    (sort, transpose)
import qualified Data.Vector                                  as V
import           GHC.IsList                                   (IsList (..))
import           Prelude                                      hiding (Fractional (..), Num (..), drop, length,
                                                               replicate, take)
import           Test.Hspec
import           Test.QuickCheck
import           Tests.NonInteractiveProof.Internal           (NonInteractiveProofTestData (..))

import           ZkFold.Base.Algebra.Basic.Class              (AdditiveGroup (..), AdditiveSemigroup (..),
                                                               MultiplicativeSemigroup (..), negate, zero, (-!))
import           ZkFold.Base.Algebra.Basic.Field              (fromZp)
import           ZkFold.Base.Algebra.Basic.Number             (value)
import           ZkFold.Base.Algebra.Polynomials.Multivariate
import           ZkFold.Base.Algebra.Polynomials.Univariate   (evalPolyVec, fromPolyVec, polyVecInLagrangeBasis,
                                                               polyVecLinear, polyVecZero, toPolyVec)
import           ZkFold.Base.Protocol.ARK.Plonk
import           ZkFold.Base.Protocol.ARK.Plonk.Internal      (fromPlonkConstraint, toPlonkArithmetization,
                                                               toPlonkConstraint)
import           ZkFold.Base.Protocol.NonInteractiveProof     (NonInteractiveProof (..))
import           ZkFold.Prelude                               (replicate, take, (!))
import           ZkFold.Symbolic.Compiler

type PlonkSizeBS = 32
type PlonkBS n = Plonk PlonkSizeBS n ByteString
type PlonkMaxPolyDegreeBS = PlonkMaxPolyDegree PlonkSizeBS

propPlonkConstraintConversion :: (F, F, F, F, F, F, F, F) -> (F, F, F) -> Bool
propPlonkConstraintConversion x (x1, x2, x3) =
    let p   = fromPlonkConstraint x
        xs  = toList $ variables p
        v   = (fromList [(head xs, x1), (xs !! 1, x2), (xs !! 2, x3)] !)
        p'  = fromPlonkConstraint $ toPlonkConstraint p
        xs' = toList $ variables p'
        v'  = (fromList [(head xs', x1), (xs' !! 1, x2), (xs' !! 2, x3)] !)
    in evalPolynomial evalMonomial v p == evalPolynomial evalMonomial v' p'

propPlonkConstraintSatisfaction :: PlonkBS n -> NonInteractiveProofTestData (PlonkBS n) -> Bool
propPlonkConstraintSatisfaction (Plonk _ _ _ ord ac _) (TestData _ w) =
    let wmap = witnessGenerator $ mapVarArithmeticCircuit ac
        (ql, qr, qo, qm, qc, a, b, c) = toPlonkArithmetization @PlonkSizeBS ord ac

        (PlonkWitnessInput wInput, _) = w
        w1'   = V.toList $ fmap ((wmap wInput !) . fromZp) (fromPolyVec a)
        w2'   = V.toList $ fmap ((wmap wInput !) . fromZp) (fromPolyVec b)
        w3'   = V.toList $ fmap ((wmap wInput !) . fromZp) (fromPolyVec c)

        input = take 2 $ fmap (negate . snd) (sort $ toList wInput)
        wPub  = input ++ replicate (value @PlonkSizeBS -! 2) zero

        ql' = V.toList $ fromPolyVec ql
        qr' = V.toList $ fromPolyVec qr
        qo' = V.toList $ fromPolyVec qo
        qm' = V.toList $ fromPolyVec qm
        qc' = V.toList $ fromPolyVec qc

        f [qlX, qrX, qoX, qmX, qcX, w1X, w2X, w3X, wPubX] =
            qlX * w1X + qrX * w2X + qoX * w3X + qmX * w1X * w2X + qcX + wPubX
        f _ = error "impossible"

    in all ((== zero) . f) $ transpose [ql', qr', qo', qm', qc', w1', w2', w3', wPub]

propPlonkPolyIdentity :: forall n . NonInteractiveProofTestData (PlonkBS n) -> Bool
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
            it "produces equivalent polynomials" $ property propPlonkConstraintConversion
        describe "Plonk constraint satisfaction" $ do
            it "should hold" $ property $ propPlonkConstraintSatisfaction @1
        describe "Plonk polynomial identity" $ do
            it "should hold" $ property $ propPlonkPolyIdentity @1
