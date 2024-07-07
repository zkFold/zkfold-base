{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

module Tests.NonInteractiveProof.Internal (NonInteractiveProofTestData(..)) where

import           Data.ByteString                                     (ByteString)
import           Prelude                                             hiding (Fractional (..), Num (..), length)
import           Test.QuickCheck                                     (Arbitrary (arbitrary), Gen)

import           ZkFold.Base.Protocol.ARK.Plonk                      (Plonk, PlonkWitnessInput (..))
import           ZkFold.Base.Protocol.NonInteractiveProof            (NonInteractiveProof (..))
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance (ArithmeticCircuitTest (witnessInput), F)

data NonInteractiveProofTestData a = TestData a (Witness a)
type PlonkSizeBS = 32
type PlonkBS n = Plonk PlonkSizeBS n ByteString

instance (Show a, Show (Input a), Show (Witness a)) =>
    Show (NonInteractiveProofTestData a) where
    show (TestData a w) = "TestData: \n" ++ show a ++ "\n" ++ show w

instance {-# INCOHERENT #-}
    (NonInteractiveProof a, Arbitrary a, Arbitrary (Witness a)) =>
    Arbitrary (NonInteractiveProofTestData a) where
    arbitrary = TestData <$> arbitrary <*> arbitrary

instance {-# OVERLAPPING #-}
    Arbitrary (NonInteractiveProofTestData (PlonkBS 1) ) where
    arbitrary = TestData <$> arbitrary <*> arbitraryW where
        arbitraryW = do
            arbACT <- arbitrary :: Gen ( ArithmeticCircuitTest 1 F )
            let witness = witnessInput arbACT
            secret <- arbitrary
            return (PlonkWitnessInput witness, secret)
