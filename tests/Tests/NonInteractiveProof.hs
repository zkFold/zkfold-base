{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module Tests.NonInteractiveProof (NonInteractiveProofTestData(..), specNonInteractiveProof) where

import           Data.Typeable                            (Proxy (..), Typeable, typeRep)
import           Prelude                                  hiding (Fractional (..), Num (..), length)
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Protocol.NonInteractiveProof (NonInteractiveProof (..))

data NonInteractiveProofTestData a = TestData a (Witness a)
instance (Show a, Show (Setup a), Show (Witness a)) => Show (NonInteractiveProofTestData a) where
    show (TestData a w) = "TestData " ++ show a ++ " " ++ show w
instance (Arbitrary a, NonInteractiveProof a, Arbitrary (Witness a)) => Arbitrary (NonInteractiveProofTestData a) where
    arbitrary = TestData <$> arbitrary <*> arbitrary

propNonInteractiveProof :: forall a . NonInteractiveProof a => NonInteractiveProofTestData a -> Bool
propNonInteractiveProof (TestData a w) =
    let s      = setup a
        (i, p) = prove @a s w
    in verify @a s i p

specNonInteractiveProof :: forall a . (Typeable a, Show a, Arbitrary a, NonInteractiveProof a,
    Show (Setup a), Show (Witness a), Arbitrary (Witness a)) => IO ()
specNonInteractiveProof = hspec $ do
    describe "Non-interactive proof protocol specification" $ do
        describe ("Type: " ++ show (typeRep (Proxy :: Proxy a))) $ do
            describe "All correct proofs" $ do
                it "should validate" $ property $ propNonInteractiveProof @a
