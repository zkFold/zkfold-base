{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE OverloadedLists     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Tests.Pairing (specPairing) where

import           Data.Typeable                              (Typeable, typeOf)
import qualified Data.Vector                                as V
import           Prelude                                    hiding (Fractional (..), Num (..), length, (^))
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.Polynomials.Univariate (PolyVec, deg, evalPolyVec, scalePV, toPolyVec, vec2poly)
import           ZkFold.Base.Protocol.Commitment.KZG        (com)

data TestPairing
instance Finite TestPairing where
    order = 32

propVerificationKZG :: forall c1 c2 t f . (Pairing c1 c2 t, f ~ ScalarField c1, f ~ ScalarField c2)
    =>f -> PolyVec f TestPairing -> f -> Bool
propVerificationKZG x p z =
    let n  = deg $ vec2poly p

        -- G1
        gs = V.fromList $ map ((`mul` gen) . (x^)) [0 .. n]
        g0 = V.head gs :: Point c1

        -- G2
        h0 = gen :: Point c2
        h1 = x `mul` h0

        -- Proving a polynomial evaluation
        pz = p `evalPolyVec` z
        h  = (p - scalePV pz one) / toPolyVec [negate z, one]
        w  = gs `com` h
        v0 = gs `com` p - (pz `mul` g0) + z `mul` w

        -- Verification
    in pairing v0 h0 == pairing w h1

specPairing :: forall c1 c2 t f . (Typeable c1, Typeable c2, Typeable t, Pairing c1 c2 t, f ~ ScalarField c1, Exponent t f) => IO ()
specPairing = hspec $ do
    describe "Elliptic curve pairing specification" $ do
        describe ("Type: " ++ show (typeOf (pairing @c1 @c2))) $ do
            describe "Pairing axioms" $ do
                it "should satisfy bilinearity" $ do
                    property $ \a b p q -> pairing @c1 @c2 (a `mul` p) (b `mul` q) == pairing p q ^ (a * b)
                it "should satisfy non-degeneracy" $ do
                    property $ \p q -> pairing @c1 @c2 p q /= one
            describe "Pairing verification" $ do
                it "should verify KZG commitments" $ do
                    property $ propVerificationKZG @c1 @c2
