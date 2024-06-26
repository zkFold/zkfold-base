{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module Tests.NonInteractiveProof (NonInteractiveProofTestData(..), specNonInteractiveProof) where

import           Data.ByteString                             (ByteString)
import           Data.Typeable                               (Proxy (..), Typeable, typeRep)
import           Prelude                                     hiding (Fractional (..), Num (..), length)
import           Test.Hspec                                  (describe, hspec, it)
import           Test.QuickCheck                             (Arbitrary (arbitrary), Testable (property))

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Base.Protocol.ARK.Plonk              (Plonk)
import           ZkFold.Base.Protocol.Commitment.KZG         (KZG)
import           ZkFold.Base.Protocol.NonInteractiveProof    (NonInteractiveProof (..))

data NonInteractiveProofTestData a = TestData a (Witness a)

instance (Show a, Show (Input a), Show (Witness a)) =>
    Show (NonInteractiveProofTestData a) where
    show (TestData a w) = "TestData: \n" ++ show a ++ "\n" ++ show w

instance (NonInteractiveProof a, Arbitrary a, Arbitrary (Witness a)) =>
    Arbitrary (NonInteractiveProofTestData a) where
    arbitrary = TestData <$> arbitrary <*> arbitrary

propNonInteractiveProof :: forall a .
    NonInteractiveProof a =>
    NonInteractiveProofTestData a -> Bool
propNonInteractiveProof (TestData a w) =
    let sp = setupProve a
        sv = setupVerify a
        (i, p) = prove @a sp w
    in verify @a sv i p

specNonInteractiveProof' :: forall a . (Typeable a, NonInteractiveProof a,
    Show a, Show (Input a), Show (Witness a),
    Arbitrary a, Arbitrary (Witness a)) => IO ()
specNonInteractiveProof' = hspec $ do
    describe "Non-interactive proof protocol specification" $ do
        describe ("Type: " ++ show (typeRep (Proxy :: Proxy a))) $ do
            describe "All correct proofs" $ do
                it "should validate" $ property $ propNonInteractiveProof @a

specNonInteractiveProof :: IO ()
specNonInteractiveProof = do
    specNonInteractiveProof' @(KZG BLS12_381_G1 BLS12_381_G2 BLS12_381_GT (Zp BLS12_381_Scalar) 32)
    specNonInteractiveProof' @(Plonk 32 2 ByteString)