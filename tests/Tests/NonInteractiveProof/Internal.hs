{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

module Tests.NonInteractiveProof.Internal (NonInteractiveProofTestData(..)) where

import           Data.ByteString                            (ByteString)
import           Data.Map                                   (fromList)
import           GHC.Natural                                (naturalToInteger)
import           GHC.Num                                    (integerToInt)
import           Prelude                                    hiding (Fractional (..), Num (..), length)
import           Test.QuickCheck                            (Arbitrary (arbitrary), Gen, vector)

import           ZkFold.Base.Protocol.ARK.Plonk             (Plonk (Plonk), PlonkWitnessInput (..))
import           ZkFold.Base.Protocol.NonInteractiveProof   (NonInteractiveProof (..))
import           ZkFold.Prelude                             (length)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit (inputVariables)
import           ZkFold.Base.Protocol.Commitment.KZG (KZG)

data NonInteractiveProofTestData a = TestData a (Witness a)
type PlonkSizeBS = 32
type PlonkBS n = Plonk PlonkSizeBS n ByteString

instance (Show a, Show (Input a), Show (Witness a)) =>
    Show (NonInteractiveProofTestData a) where
    show (TestData a w) = "TestData: \n" ++ show a ++ "\n" ++ show w

instance (NonInteractiveProof (KZG c1 c2 t f d), Arbitrary (KZG c1 c2 t f d), Arbitrary (Witness (KZG c1 c2 t f d))) =>
    Arbitrary (NonInteractiveProofTestData (KZG c1 c2 t f d)) where
    arbitrary = TestData <$> arbitrary <*> arbitrary

instance Arbitrary (NonInteractiveProofTestData (PlonkBS 2) ) where
    arbitrary = do
        rbPlonk@(Plonk _ _ _ _ ac _) <- arbitrary :: Gen (PlonkBS 2)
        let keysAC = inputVariables ac
        values <- vector . integerToInt . naturalToInteger . length  $ keysAC
        let wi = fromList $ zip keysAC values
        secret <- arbitrary
        return $ TestData rbPlonk (PlonkWitnessInput wi, secret)
