{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Tests.Pairing (specPairing) where

import           Data.Kind                                   (Type)
import           Data.Typeable                               (Typeable, typeOf)
import qualified Data.Vector                                 as V
import           Prelude                                     hiding (Fractional (..), Num (..), length, (^))
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Algebra.EllipticCurve.BN254
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.Polynomials.Univariate  (PolyVec, deg, evalPolyVec, polyVecDiv, scalePV, toPolyVec,
                                                              vec2poly)
import           ZkFold.Base.Protocol.NonInteractiveProof    (CoreFunction (..), HaskellCore, msm)

propVerificationKZG
    :: forall c1 c2 f core
    .  Pairing c1 c2
    => f ~ ScalarField c1
    => f ~ ScalarField c2
    => Field f
    => Eq f
    => AdditiveGroup (BaseField c1)
    => CoreFunction c1 core
    => f -> PolyVec f 32 -> f -> Bool
propVerificationKZG x p z =
    let n  = deg $ vec2poly p

        -- G1
        gs = V.fromList $ map ((`mul` gen) . (x^)) [0 .. n]
        g0 = V.head gs :: Point c1

        -- G2
        h0 = gen :: Point c2
        h1 = x `mul` h0

        com = msm @c1 @core
        -- Proving a polynomial evaluation
        pz = p `evalPolyVec` z
        h  = (p - scalePV pz one) `polyVecDiv` toPolyVec [negate z, one]
        w  = gs `com` h
        v0 = gs `com` p - (pz `mul` g0) + z `mul` w

        -- Verification
    in pairing v0 h0 == pairing w h1

specPairing'
    :: forall (c1 :: Type) (c2 :: Type) f
    .  Typeable c1
    => Typeable c2
    => Typeable (TargetGroup c1 c2)
    => Pairing c1 c2
    => f ~ ScalarField c1
    => Field f
    => Eq f
    => Show f
    => Arbitrary f
    => Eq (BaseField c2)
    => Show (BaseField c2)
    => AdditiveGroup (BaseField c1)
    => Eq (BaseField c1)
    => Show (BaseField c1)
    => IO ()
specPairing' = hspec $ do
    describe "Elliptic curve pairing specification" $ do
        describe ("Type: " ++ show (typeOf (pairing @c1 @c2))) $ do
            describe "Pairing axioms" $ do
                it "should satisfy bilinearity" $ withMaxSuccess 10 $ do
                    property $ \a b p q ->
                        pairing @c1 @c2 (a `mul` p) (b `mul` q)
                            == pairing p q ^ (a * b)
                it "should satisfy non-degeneracy" $ withMaxSuccess 10 $ do
                    property $ \p q ->
                        (p /= zero && q /= zero) ==> pairing @c1 @c2 p q /= one
            describe "Pairing verification" $ do
                it "should verify KZG commitments" $ withMaxSuccess 10 $ do
                    property $ propVerificationKZG @c1 @c2 @f @HaskellCore

specPairing :: IO ()
specPairing = do
    specPairing' @BN254_G1 @BN254_G2
    specPairing' @BLS12_381_G1 @BLS12_381_G2
