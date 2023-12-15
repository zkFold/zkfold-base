module Tests.Pairing (specPairing) where

import           Data.Typeable                               (typeOf)
import           Prelude                                     hiding (Num(..), Fractional(..), (^), length)
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (pairing, BLS12_381_G1)
import           ZkFold.Base.Algebra.EllipticCurve.Class     (EllipticCurve(..), ScalarField)
import           ZkFold.Base.Algebra.Polynomials.Univariate  (PolyVec, scalePV, evalPolyVec, toPolyVec, vec2poly, deg)
import           ZkFold.Base.Protocol.Commitment.KZG         (com)

-- TODO: make this test polymorphic in the elliptic curve

data TestPairing
instance Finite TestPairing where
    order = 32

propVerificationKZG :: ScalarField BLS12_381_G1 -> PolyVec (ScalarField BLS12_381_G1) TestPairing -> ScalarField BLS12_381_G1 -> Bool
propVerificationKZG x p z =
    let n  = deg $ vec2poly p

        -- G1
        gs = map ((`mul` gen) . (x^)) [0 .. n]
        g0 = head gs

        -- G2
        h0 = gen
        h1 = x `mul` h0

        -- Proving a polynomial evaluation
        pz = p `evalPolyVec` z
        h  = (p - scalePV pz one) / toPolyVec [negate z, one]
        w  = gs `com` h
        v0 = gs `com` p - (pz `mul` g0) + z `mul` w

        -- Verification
    in pairing v0 h0 == pairing w h1

specPairing :: IO ()
specPairing = hspec $ do
    describe "Elliptic curve pairing specification" $ do
        describe ("Type: " ++ show (typeOf pairing)) $ do
            describe "Pairing axioms" $ do
                it "should satisfy bilinearity" $ do
                    property $ \a b p q -> pairing (a `mul` p) (b `mul` q) == pairing p q ^ (a * b)
                it "should satisfy non-degeneracy" $ do
                    property $ \p q -> pairing p q /= one
            describe "Pairing verification" $ do
                it "should verify KZG commitments" $ do
                    property propVerificationKZG