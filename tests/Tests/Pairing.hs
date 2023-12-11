module Tests.Pairing (specPairing) where

import           Data.Typeable                               (typeOf)
import           Prelude                                     hiding (Num(..), Fractional(..), (^), length)
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (pairing)
import           ZkFold.Base.Algebra.EllipticCurve.Class     (EllipticCurve(..))

specPairing :: IO ()
specPairing = hspec $ do
    describe "Elliptic curve pairing specification" $ do
        describe ("Type: " ++ show (typeOf pairing)) $ do
            describe "Pairing axioms" $ do
                it "should satisfy bilinearity" $ do
                    property $ \a b p q -> pairing (a `mul` p) (b `mul` q) == pairing p q ^ (a * b)
                it "should satisfy non-degeneracy" $ do
                    property $ \p q -> pairing p q /= one