{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

module Tests.NonInteractiveProof.Internal (NonInteractiveProofTestData(..)) where

import           Data.ByteString                                     (ByteString)
import           Prelude                                             hiding (Fractional (..), Num (..), length)
import           Test.QuickCheck                                     (Arbitrary (arbitrary), Gen)

import           ZkFold.Base.Data.Vector                             (Vector (..))
import           ZkFold.Base.Protocol.ARK.Plonk                      (F, Plonk (Plonk), PlonkWitnessInput (..),
                                                                      genSubset)
import           ZkFold.Base.Protocol.ARK.Plonk.Internal             (getParams)
import           ZkFold.Base.Protocol.Commitment.KZG                 (KZG)
import           ZkFold.Base.Protocol.NonInteractiveProof            (NonInteractiveProof (..))
import           ZkFold.Prelude                                      (length)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit          (inputVariables)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance (ArithmeticCircuitTest (..))
import GHC.TypeNats (KnownNat)
import ZkFold.Base.Algebra.Basic.Number (value)

data NonInteractiveProofTestData a = TestData a (Witness a)
type PlonkSizeBS = 32
type PlonkBS n = Plonk PlonkSizeBS n ByteString

instance (Show a, Show (Input a), Show (Witness a)) =>
    Show (NonInteractiveProofTestData a) where
    show (TestData a w) = "TestData: \n" ++ show a ++ "\n" ++ show w

instance (NonInteractiveProof (KZG c1 c2 t f d), Arbitrary (KZG c1 c2 t f d), Arbitrary (Witness (KZG c1 c2 t f d))) =>
    Arbitrary (NonInteractiveProofTestData (KZG c1 c2 t f d)) where
    arbitrary = TestData <$> arbitrary <*> arbitrary

instance forall n . (KnownNat n) => Arbitrary (NonInteractiveProofTestData (PlonkBS n) ) where
    arbitrary = do
        ArithmeticCircuitTest ac wi <- arbitrary :: Gen (ArithmeticCircuitTest 1 F)
        let inputLen = length . inputVariables $ ac
        vecPubInp <- genSubset (return []) (value @n) inputLen
        let (omega, k1, k2) = getParams 32
        pl <- Plonk omega k1 k2 (Vector vecPubInp) ac <$> arbitrary
        secret <- arbitrary
        return $ TestData pl (PlonkWitnessInput wi, secret)
