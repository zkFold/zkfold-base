{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module Tests.NonInteractiveProof (NonInteractiveProofTestData(..), specNonInteractiveProof) where

import           Data.Typeable                            (Proxy (..), Typeable, typeRep)
import           Prelude                                  hiding (Fractional (..), Num (..), length)
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Protocol.NonInteractiveProof (NonInteractiveProof (..))

data NonInteractiveProofTestData a = TestData a (Input a) (Witness a)

instance (Show a, Show (Input a), Show (Witness a)) =>
    Show (NonInteractiveProofTestData a) where
    show (TestData a i w) = "TestData: \n" ++ show a ++ "\n" ++ show i ++ "\n" ++ show w

instance (NonInteractiveProof a, Arbitrary a, Arbitrary (Input a), Arbitrary (Witness a)) =>
    Arbitrary (NonInteractiveProofTestData a) where
    arbitrary = TestData <$> arbitrary <*> arbitrary <*> arbitrary

propNonInteractiveProof :: forall a .
    NonInteractiveProof a =>
    NonInteractiveProofTestData a -> Bool
propNonInteractiveProof (TestData a i w) =
    let s = setup a
        p = prove @a s i w
    in verify @a s i p

specNonInteractiveProof :: forall a . (Typeable a, NonInteractiveProof a,
    Show a, Show (Input a), Show (Witness a),
    Arbitrary a, Arbitrary (Input a), Arbitrary (Witness a)) => IO ()
specNonInteractiveProof = hspec $ do
    describe "Non-interactive proof protocol specification" $ do
        describe ("Type: " ++ show (typeRep (Proxy :: Proxy a))) $ do
            describe "All correct proofs" $ do
                it "should validate" $ property $ propNonInteractiveProof @a
