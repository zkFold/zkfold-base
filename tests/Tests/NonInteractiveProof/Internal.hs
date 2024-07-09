{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

module Tests.NonInteractiveProof.Internal (NonInteractiveProofTestData(..)) where

import           Data.ByteString                            (ByteString)
import           Prelude                                    hiding (Fractional (..), Num (..), length)
import           Test.QuickCheck                            (Arbitrary (arbitrary), Gen)

import ZkFold.Base.Protocol.ARK.Plonk ( Plonk(Plonk), PlonkWitnessInput(..), genSubset, F )
import           ZkFold.Base.Protocol.Commitment.KZG        (KZG)
import           ZkFold.Base.Protocol.NonInteractiveProof   (NonInteractiveProof (..))
import           ZkFold.Prelude                             (length)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit (inputVariables)
import ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance (ArithmeticCircuitTest(..))
import           ZkFold.Base.Protocol.ARK.Plonk.Internal             (getParams)
import ZkFold.Base.Data.Vector (Vector(..))
import Data.Map ( fromList, (!) )

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
        ArithmeticCircuitTest ac wi <- arbitrary :: Gen (ArithmeticCircuitTest 1 F)

        let fullInp = length . inputVariables $ ac
        vecPubInp <- genSubset (return []) 2 fullInp
        let (omega, k1, k2) = getParams 2

        let wi' = fromList $ [(k, wi ! k) | k <- vecPubInp]

        pl <- Plonk omega k1 k2 (Vector vecPubInp) ac <$> arbitrary
        secret <- arbitrary

        return $ TestData pl (PlonkWitnessInput wi', secret)