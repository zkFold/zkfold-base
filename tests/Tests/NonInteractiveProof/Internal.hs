{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

module Tests.NonInteractiveProof.Internal (NonInteractiveProofTestData(..)) where

import           Data.ByteString                                     (ByteString)
import           Prelude                                             hiding (Fractional (..), Num (..), length)
import           Test.QuickCheck                                     (Arbitrary (arbitrary), Gen, vector)

import           ZkFold.Base.Protocol.ARK.Plonk                      (Plonk (Plonk), PlonkWitnessInput (..))
import           ZkFold.Base.Protocol.NonInteractiveProof            (NonInteractiveProof (..))
import ZkFold.Symbolic.Compiler.ArithmeticCircuit (inputVariables)
import           GHC.Natural                                               (naturalToInteger)
import           GHC.Num                                                   (integerToInt)
import           ZkFold.Prelude                                            (length)
import Data.Map (fromList)

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
    arbitrary = do
        rbPlonk@(Plonk _ _ _ _ ac _) <- arbitrary :: Gen (PlonkBS 1)
        let keysAC = inputVariables ac
        values <- vector . integerToInt . naturalToInteger . length  $ keysAC
        let wi = fromList $ zip keysAC values
        secret <- arbitrary
        return $ TestData rbPlonk (PlonkWitnessInput wi, secret)