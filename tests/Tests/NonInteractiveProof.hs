{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module Tests.NonInteractiveProof (NonInteractiveProofTestData(..), specNonInteractiveProof) where

import           Data.Typeable                            (Proxy (..), Typeable, typeRep)
import           Prelude                                  hiding (Num(..), Fractional(..), length)
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Protocol.NonInteractiveProof (NonInteractiveProof(..))

data NonInteractiveProofTestData a = TestData (Setup a) (ProverSecret a) (Witness a)
instance (Show (Setup a), Show (ProverSecret a), Show (Witness a)) => Show (NonInteractiveProofTestData a) where
    show (TestData s ps w) = "TestData " ++ show s ++ " " ++ show ps ++ " " ++ show w
instance (NonInteractiveProof a, Arbitrary (Params a), Arbitrary (SetupSecret a), Arbitrary (ProverSecret a), Arbitrary (Witness a))
        => Arbitrary (NonInteractiveProofTestData a) where
    arbitrary = do
        s <- setup @a <$> arbitrary <*> arbitrary
        TestData s <$> arbitrary <*> arbitrary

propNonInteractiveProof :: forall a . NonInteractiveProof a => NonInteractiveProofTestData a -> Bool
propNonInteractiveProof (TestData s ps w) =
    let (i, p) = prove @a ps s w
    in verify @a s i p

specNonInteractiveProof :: forall a . (Typeable a, NonInteractiveProof a, Show (Setup a), Show (ProverSecret a), Show (Witness a),
    Arbitrary (Params a), Arbitrary (SetupSecret a), Arbitrary (ProverSecret a), Arbitrary (Witness a)) => IO ()
specNonInteractiveProof = hspec $ do
    describe "Non-interactive proof protocol specification" $ do
        describe ("Type: " ++ show (typeRep (Proxy :: Proxy a))) $ do
            describe "All correct proofs" $ do
                it "should validate" $ property $ propNonInteractiveProof @a