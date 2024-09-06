{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.Plonkup (PlonkBS, specPlonkup) where

import           Data.ByteString                                     (ByteString)
import           GHC.IsList                                          (IsList (..))
import           Prelude                                             hiding (Fractional (..), Num (..), drop, length,
                                                                      replicate, take)
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class                     (AdditiveGroup (..), AdditiveSemigroup (..), MultiplicativeSemigroup (..),
                                                                      FiniteField, FromConstant (..), Scale (..),
                                                                      negate, zero)
import           ZkFold.Base.Algebra.Basic.Field                     (fromZp)
import           ZkFold.Base.Algebra.Basic.Number                    (KnownNat)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381         (BLS12_381_G1, BLS12_381_G2)
import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..))
import           ZkFold.Base.Algebra.Polynomials.Univariate          ((.*.), toPolyVec, evalPolyVec)
import           ZkFold.Base.Data.Vector                             (Vector, fromVector)
import           ZkFold.Base.Protocol.NonInteractiveProof            (HaskellCore, setupProve)
import           ZkFold.Base.Protocol.Plonkup                        hiding (omega)
import           ZkFold.Base.Protocol.Plonkup.PlonkConstraint
import           ZkFold.Base.Protocol.Plonkup.Prover                 (plonkupProve)
import           ZkFold.Base.Protocol.Plonkup.Prover.Secret
import           ZkFold.Base.Protocol.Plonkup.Prover.Setup           (PlonkupProverSetup(..))
import           ZkFold.Base.Protocol.Plonkup.Relation               (PlonkupRelation (..))
import           ZkFold.Base.Protocol.Plonkup.Testing
import           ZkFold.Base.Protocol.Plonkup.Witness                (PlonkupWitnessInput)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

type PlonkPolyLengthBS = 32
type PlonkBS l = Plonkup 1 PlonkPolyLengthBS l BLS12_381_G1 BLS12_381_G2 ByteString

propPlonkConstraintConversion :: (Eq a, Scale a a, FromConstant a a, FiniteField a) => PlonkConstraint 1 a -> Bool
propPlonkConstraintConversion p =
    toPlonkConstraint (fromPlonkConstraint p) == p

propPlonkupRelationHolds :: forall i n l a . (KnownNat n, Arithmetic a) => PlonkupRelation i n l a -> Vector i a -> Bool
propPlonkupRelationHolds PlonkupRelation {..} w =
    let (w1, w2, w3) = witness w
        pub          = negate $ toPolyVec $ fromList $ fromVector $ pubInput w
    in qL .*. w1 + qR .*. w2 + qO .*. w3 + qM .*. w1 .*. w2 + qC + pub == zero

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
    in p `evalPolyVec` (omega setup ^ fromZp pow) == zero

specPlonkup :: IO ()
specPlonkup = hspec $ do
    describe "Plonkup specification" $ do
        describe "Conversion to Plonk constraints and back" $ do
            it "produces equivalent polynomials" $ property $ propPlonkConstraintConversion @(ScalarField BLS12_381_G1)
        describe "Plonkup relation" $ do
            it "should hold" $ property $ propPlonkupRelationHolds @2 @32 @3 @(ScalarField BLS12_381_G1)
        describe "Plonk polynomials equality" $ do
            it "should hold" $ property $ propPlonkPolyEquality @1 @32 @2
