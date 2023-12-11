{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.NonInteractiveProof (specNonInteractiveProof) where

import           Data.Typeable                            (Proxy (..), typeRep)
import           Prelude                                  hiding (Num(..), Fractional(..), length)
import           Test.Hspec
import           Test.QuickCheck

import           ZkFold.Base.Protocol.NonInteractiveProof (NonInteractiveProof(..))

data TestData a = TestData (Setup a) (ProverSecret a) (Witness a)
instance NonInteractiveProof a => Show (TestData a) where
    show (TestData s ps w) = "TestData " ++ show s ++ " " ++ show ps ++ " " ++ show w
instance NonInteractiveProof a => Arbitrary (TestData a) where
    arbitrary = do
        s <- setup @a <$> arbitrary <*> arbitrary
        TestData s <$> arbitrary <*> arbitrary

propNonInteractiveProof :: forall a . NonInteractiveProof  a => TestData a -> Bool
propNonInteractiveProof (TestData s ps w) =
    let (i, p) = prove @a ps s w
    in verify @a s i p

specNonInteractiveProof :: forall a . (NonInteractiveProof a) => IO ()
specNonInteractiveProof = hspec $ do
    describe "Non-interactive proof protocool specification" $ do
        describe ("Type: " ++ show (typeRep (Proxy :: Proxy a))) $ do
            describe "All correct proofs" $ do
                it "should validate" $ property $ propNonInteractiveProof @a