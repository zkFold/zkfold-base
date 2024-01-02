{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.Plonk (specPlonk) where

import           Data.Containers.ListUtils                    (nubOrd)
import           Data.List                                    (transpose)
import           Data.Map                                     (keys, fromList, singleton, elems)
import           Prelude                                      hiding (Num(..), Fractional(..), length, take, drop, replicate)
import           Test.Hspec
import           Test.QuickCheck

import           Tests.NonInteractiveProof                    (NonInteractiveProofTestData(..))

import           ZkFold.Base.Algebra.Basic.Class              (AdditiveSemigroup (..), AdditiveGroup (..), MultiplicativeSemigroup (..), Finite (..), zero, negate)
import           ZkFold.Base.Algebra.Basic.Field              (fromZp)
import           ZkFold.Base.Algebra.Polynomials.Multivariate (getPowers, getMonomials, evalMultivariate)
import           ZkFold.Base.Algebra.Polynomials.Univariate   (toPolyVec, polyVecInLagrangeBasis, fromPolyVec, polyVecZero, polyVecLinear, evalPolyVec)
import           ZkFold.Base.Protocol.ARK.Plonk
import           ZkFold.Base.Protocol.ARK.Plonk.Internal      (fromPlonkConstraint, toPlonkConstaint, toPlonkArithmetization)
import           ZkFold.Prelude                               ((!), take, replicate)
import           ZkFold.Symbolic.Arithmetization              (ArithmeticCircuit (..), mapVarArithmeticCircuit)

propPlonkConstraintConversion :: (F, F, F, F, F, F, F, F) -> (F, F, F) -> Bool
propPlonkConstraintConversion x (x1, x2, x3) =
    let p   = fromPlonkConstraint x
        xs  = nubOrd $ concatMap (keys . getPowers) (getMonomials p)
        v   = fromList [(head xs, x1), (xs !! 1, x2), (xs !! 2, x3)]
        p'  = fromPlonkConstraint $ toPlonkConstaint p
        xs' = nubOrd $ concatMap (keys . getPowers) (getMonomials p)
        v'  = fromList [(head xs', x1), (xs' !! 1, x2), (xs' !! 2, x3)]
    in p `evalMultivariate` v == p' `evalMultivariate` v'

propPlonkConstraintSatisfaction :: ParamsPlonk -> NonInteractiveProofTestData PlonkBS -> Bool
propPlonkConstraintSatisfaction (ParamsPlonk _ _ _ inputs ac) (TestData _ _ w) =
    let wmap = acWitness $ mapVarArithmeticCircuit ac
        (ql, qr, qo, qm, qc, a, b, c) = toPlonkArithmetization @PlonkBS (singleton (acOutput ac) 15) ac
        l = 1

        WitnessInputPlonk wInput = w
        w1'     = map ((wmap wInput !) . fromZp) (fromPolyVec a)
        w2'     = map ((wmap wInput !) . fromZp) (fromPolyVec b)
        w3'     = map ((wmap wInput !) . fromZp) (fromPolyVec c)
        wPub    = take l (map negate $ elems inputs) ++ replicate (order @PlonkBS - l) zero
        
        ql' = fromPolyVec ql
        qr' = fromPolyVec qr
        qo' = fromPolyVec qo
        qm' = fromPolyVec qm
        qc' = fromPolyVec qc

        f [qlX, qrX, qoX, qmX, qcX, w1X, w2X, w3X, wPubX] =
            qlX * w1X + qrX * w2X + qoX * w3X + qmX * w1X * w2X + qcX + wPubX
        f _ = error "impossible"

    in all ((== zero) . f) $ transpose [ql', qr', qo', qm', qc', w1', w2', w3', wPub]

propPlonkPolyIdentity :: NonInteractiveProofTestData PlonkBS -> Bool
propPlonkPolyIdentity (TestData s ps w) =
    let zH = polyVecZero @F @PlonkBS @PlonkMaxPolyDegreeBS

        ((wPub, _, _, _, omega, _, _), (qlE, qrE, qoE, qmE, qcE, _, _, _), _, WitnessMap wmap, _) = s
        ProverSecretPlonk b1 b2 b3 b4 b5 b6 _ _ _ _ _ = ps
        WitnessInputPlonk wInput = w
        (w1, w2, w3) = wmap wInput
        pubPoly = polyVecInLagrangeBasis @F @PlonkBS @PlonkMaxPolyDegreeBS omega $ toPolyVec @F @PlonkBS wPub

        a = polyVecLinear b2 b1 * zH + polyVecInLagrangeBasis omega w1
        b = polyVecLinear b4 b3 * zH + polyVecInLagrangeBasis omega w2
        c = polyVecLinear b6 b5 * zH + polyVecInLagrangeBasis omega w3

        f x =
            let qlX = qlE `evalPolyVec` x
                qrX = qrE `evalPolyVec` x
                qoX = qoE `evalPolyVec` x
                qmX = qmE `evalPolyVec` x
                qcX = qcE `evalPolyVec` x
                aX = a `evalPolyVec` x
                bX = b `evalPolyVec` x
                cX = c `evalPolyVec` x
                pubX = pubPoly `evalPolyVec` x
            in qlX * aX + qrX * bX + qoX * cX + qmX * aX * bX + qcX + pubX

    in all ((== zero) . f . (omega^)) [0 .. order @PlonkBS - 1]

specPlonk :: IO ()
specPlonk = hspec $ do
    describe "Plonk specification" $ do
        describe "Conversion to Plonk constraints and back" $ do
            it "produces equivalent polynomials" $ property propPlonkConstraintConversion
        describe "Plonk constraint satisfaction" $ do
            it "should hold" $ property propPlonkConstraintSatisfaction
        describe "Plonk polynomial identity" $ do
            it "should hold" $ property propPlonkPolyIdentity