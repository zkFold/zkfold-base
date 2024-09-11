{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.Plonkup (specPlonkup) where

import           Data.ByteString                                     (ByteString)
import           Data.List                                           (sort)
import           GHC.IsList                                          (IsList (..))
import           Prelude                                             hiding (Fractional (..), Num (..), drop, length,
                                                                      replicate, take)
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class                     (AdditiveGroup (..), AdditiveSemigroup (..), MultiplicativeSemigroup (..),
                                                                      FiniteField, FromConstant (..), Scale (..),
                                                                      negate, zero, one)
import           ZkFold.Base.Algebra.Basic.Field                     (fromZp)
import           ZkFold.Base.Algebra.Basic.Number                    (KnownNat)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381         (BLS12_381_G1, BLS12_381_G2)
import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..))
import           ZkFold.Base.Algebra.Polynomials.Univariate
import           ZkFold.Base.Data.Vector                             (Vector, fromVector)
import           ZkFold.Base.Protocol.NonInteractiveProof            (HaskellCore, setupProve)
import           ZkFold.Base.Protocol.Plonkup                        hiding (omega)
import           ZkFold.Base.Protocol.Plonkup.PlonkConstraint
import           ZkFold.Base.Protocol.Plonkup.Prover                 (plonkupProve)
import           ZkFold.Base.Protocol.Plonkup.Prover.Secret
import           ZkFold.Base.Protocol.Plonkup.Relation               (PlonkupRelation (..))
import           ZkFold.Base.Protocol.Plonkup.Testing
import           ZkFold.Base.Protocol.Plonkup.Utils                  (sortByList)
import           ZkFold.Base.Protocol.Plonkup.Witness                (PlonkupWitnessInput)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

propPlonkConstraintConversion :: (Eq a, Scale a a, FromConstant a a, FiniteField a) => PlonkConstraint 1 a -> Bool
propPlonkConstraintConversion p =
    toPlonkConstraint (fromPlonkConstraint p) == p

propPlonkupRelationHolds :: forall i n l a . (KnownNat n, Arithmetic a) => PlonkupRelation i n l a -> Vector i a -> Bool
propPlonkupRelationHolds PlonkupRelation {..} w =
    let (w1, w2, w3) = witness w
        pub          = negate $ toPolyVec $ fromList $ fromVector $ pubInput w
    in qL .*. w1 + qR .*. w2 + qO .*. w3 + qM .*. w1 .*. w2 + qC + pub == zero

propSortByListIsCorrect :: Ord a => [a] -> Bool
propSortByListIsCorrect xs = sortByList xs (sort xs) == sort xs

propPlonkPolyEquality :: (KnownNat i, KnownNat n, KnownNat (PlonkupPermutationSize n), KnownNat (PlonkupPolyExtendedLength n), KnownNat l)
    => Plonkup i n l BLS12_381_G1 BLS12_381_G2 ByteString
    -> PlonkupWitnessInput i BLS12_381_G1
    -> PlonkupProverSecret BLS12_381_G1
    -> ScalarField BLS12_381_G1
    -> Bool
propPlonkPolyEquality plonk witness secret pow =
    let setup = setupProve @_ @HaskellCore plonk
        (_, _, PlonkupProverTestInfo {..}) = plonkupProve @_ @_ @_ @_ @_ @ByteString @HaskellCore setup (witness, secret)
        p = qmX * aX * bX + qlX * aX + qrX * bX + qoX * cX + piX + qcX
    in p `evalPolyVec` (omega ^ fromZp pow) == zero

propPlonkGrandProductIsCorrect :: (KnownNat i, KnownNat n, KnownNat (PlonkupPermutationSize n), KnownNat (PlonkupPolyExtendedLength n), KnownNat l)
    => Plonkup i n l BLS12_381_G1 BLS12_381_G2 ByteString
    -> PlonkupWitnessInput i BLS12_381_G1
    -> PlonkupProverSecret BLS12_381_G1
    -> Bool
propPlonkGrandProductIsCorrect plonk witness secret =
    let setup = setupProve @_ @HaskellCore plonk
        (_, _, PlonkupProverTestInfo {..}) = plonkupProve @_ @_ @_ @_ @_ @ByteString @HaskellCore setup (witness, secret)
    in head (toList $ fromPolyVec grandProduct1) == one

propPlonkGrandProductEquality :: (KnownNat i, KnownNat n, KnownNat (PlonkupPermutationSize n), KnownNat (PlonkupPolyExtendedLength n), KnownNat l)
    => Plonkup i n l BLS12_381_G1 BLS12_381_G2 ByteString
    -> PlonkupWitnessInput i BLS12_381_G1
    -> PlonkupProverSecret BLS12_381_G1
    -> ScalarField BLS12_381_G1
    -> Bool
propPlonkGrandProductEquality plonk witness secret pow =
    let setup = setupProve @_ @HaskellCore plonk
        (_, _, PlonkupProverTestInfo {..}) = plonkupProve @_ @_ @_ @_ @_ @ByteString @HaskellCore setup (witness, secret)

        gammaX = scalePV gamma one
        p =   (aX + polyVecLinear beta gamma)
            * (bX + polyVecLinear (beta * k1) gamma)
            * (cX + polyVecLinear (beta * k2) gamma)
            * z1X .* alpha
            - (aX + (beta *. s1X) + gammaX)
            * (bX + (beta *. s2X) + gammaX)
            * (cX + (beta *. s3X) + gammaX)
            * (z1X .*. omegas') .* alpha
    in p `evalPolyVec` (omega ^ fromZp pow) == zero

propLookupPolyEquality :: (KnownNat i, KnownNat n, KnownNat (PlonkupPermutationSize n), KnownNat (PlonkupPolyExtendedLength n), KnownNat l)
    => Plonkup i n l BLS12_381_G1 BLS12_381_G2 ByteString
    -> PlonkupWitnessInput i BLS12_381_G1
    -> PlonkupProverSecret BLS12_381_G1
    -> ScalarField BLS12_381_G1
    -> Bool
propLookupPolyEquality plonk witness secret pow =
    let setup = setupProve @_ @HaskellCore plonk
        (_, _, PlonkupProverTestInfo {..}) = plonkupProve @_ @_ @_ @_ @_ @ByteString @HaskellCore setup (witness, secret)

        p = qkX * (aX - fX)
    in p `evalPolyVec` (omega ^ fromZp pow) == zero

propLookupGrandProductIsCorrect :: (KnownNat i, KnownNat n, KnownNat (PlonkupPermutationSize n), KnownNat (PlonkupPolyExtendedLength n), KnownNat l)
    => Plonkup i n l BLS12_381_G1 BLS12_381_G2 ByteString
    -> PlonkupWitnessInput i BLS12_381_G1
    -> PlonkupProverSecret BLS12_381_G1
    -> Bool
propLookupGrandProductIsCorrect plonk witness secret =
    let setup = setupProve @_ @HaskellCore plonk
        (_, _, PlonkupProverTestInfo {..}) = plonkupProve @_ @_ @_ @_ @_ @ByteString @HaskellCore setup (witness, secret)
    in z2X `evalPolyVec` omega == one

propLookupGrandProductEquality :: (KnownNat i, KnownNat n, KnownNat (PlonkupPermutationSize n), KnownNat (PlonkupPolyExtendedLength n), KnownNat l)
    => Plonkup i n l BLS12_381_G1 BLS12_381_G2 ByteString
    -> PlonkupWitnessInput i BLS12_381_G1
    -> PlonkupProverSecret BLS12_381_G1
    -> ScalarField BLS12_381_G1
    -> Bool
propLookupGrandProductEquality plonk witness secret pow =
    let setup = setupProve @_ @HaskellCore plonk
        (_, _, PlonkupProverTestInfo {..}) = plonkupProve @_ @_ @_ @_ @_ @ByteString @HaskellCore setup (witness, secret)

        deltaX   = scalePV delta one
        epsilonX = scalePV epsilon one
        p =   z2X * (one + deltaX) * (epsilonX + fX) * ((epsilonX * (one + deltaX)) + tX + deltaX * (tX .*. omegas'))
            - (z2X .*. omegas') * ((epsilonX * (one + deltaX)) + h1X + deltaX * h2X) * ((epsilonX * (one + deltaX)) + h2X + deltaX * (h1X .*. omegas'))
    in p `evalPolyVec` (omega ^ fromZp pow) == zero

propLinearizationPolyEvaluation :: forall i n l . (KnownNat i, KnownNat n, KnownNat (PlonkupPermutationSize n), KnownNat (PlonkupPolyExtendedLength n), KnownNat l)
    => Plonkup i n l BLS12_381_G1 BLS12_381_G2 ByteString
    -> PlonkupWitnessInput i BLS12_381_G1
    -> PlonkupProverSecret BLS12_381_G1
    -> Bool
propLinearizationPolyEvaluation plonk witness secret =
    let setup = setupProve @_ @HaskellCore plonk
        (_, _, PlonkupProverTestInfo {..}) = plonkupProve @_ @_ @_ @_ @_ @ByteString @HaskellCore setup (witness, secret)
    in rX `evalPolyVec` xi == zero

specPlonkup :: IO ()
specPlonkup = hspec $ do
    describe "Plonkup specification" $ do
        describe "Conversion to Plonk constraints and back" $ do
            it "produces equivalent polynomials" $ property $ propPlonkConstraintConversion @(ScalarField BLS12_381_G1)
        describe "Sort by list is correct" $ do
            it "should hold" $ property $ propSortByListIsCorrect @Int
        describe "Plonkup relation" $ do
            it "should hold" $ property $ propPlonkupRelationHolds @2 @32 @3 @(ScalarField BLS12_381_G1)
        describe "Plonk polynomials equality" $ do
            it "should hold" $ property $ propPlonkPolyEquality @1 @32 @2
        describe "Plonk grand product correctness" $ do
            it "should hold" $ property $ withMaxSuccess 10 $ propPlonkGrandProductIsCorrect @1 @32 @2
        describe "Plonkup grand product equality" $ do
            it "should hold" $ property $ withMaxSuccess 10 $ propPlonkGrandProductEquality @1 @32 @2
        describe "Lookup polynomials equality" $ do
            it "should hold" $ property $ withMaxSuccess 10 $ propLookupPolyEquality @1 @32 @2
        describe "Lookup grand product correctness" $ do
            it "should hold" $ property $ withMaxSuccess 10 $ propLookupGrandProductIsCorrect @1 @32 @2
        describe "Lookup grand product equality" $ do
            it "should hold" $ property $ withMaxSuccess 10 $ propLookupGrandProductEquality @1 @32 @2
        describe "Linearization polynomial in the challenge point" $ do
            it "evaluates to zero" $ property $ withMaxSuccess 10 $ propLinearizationPolyEvaluation @1 @32 @2
