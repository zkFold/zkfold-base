{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

module Tests.NonInteractiveProof.Internal (NonInteractiveProofTestData(..)) where

import           Prelude                                     hiding (Fractional (..), Num (..), length)
import           Test.QuickCheck                             (Arbitrary (arbitrary))

import           ZkFold.Base.Protocol.NonInteractiveProof    (NonInteractiveProof (..))

data NonInteractiveProofTestData a = TestData a (Witness a)

instance (Show a, Show (Input a), Show (Witness a)) =>
    Show (NonInteractiveProofTestData a) where
    show (TestData a w) = "TestData: \n" ++ show a ++ "\n" ++ show w

instance (NonInteractiveProof a, Arbitrary a, Arbitrary (Witness a)) =>
    Arbitrary (NonInteractiveProofTestData a) where
    arbitrary = TestData <$> arbitrary <*> arbitrary