{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Tests.NonInteractiveProof.Internal (NonInteractiveProofTestData(..)) where

import           Data.ByteString                                (ByteString)
import           GHC.Generics                                   (Par1)
import           GHC.TypeNats                                   (KnownNat)
import           Prelude                                        hiding (Fractional (..), Num (..), length)
import           Test.QuickCheck                                (Arbitrary (arbitrary), Gen)

import           ZkFold.Base.Algebra.Basic.Number               (value)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381    (BLS12_381_G1, BLS12_381_G2)
import           ZkFold.Base.Algebra.EllipticCurve.Class        (EllipticCurve (..))
import           ZkFold.Base.Data.Vector                        (Vector (..))
import           ZkFold.Base.Protocol.ARK.Plonk                 (Plonk (Plonk), PlonkWitnessInput (..), genSubset,
                                                                 getParams)
import           ZkFold.Base.Protocol.Commitment.KZG            (KZG)
import           ZkFold.Base.Protocol.NonInteractiveProof       (NonInteractiveProof (..))
import           ZkFold.Prelude                                 (length)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit     (inputVariables, witnessGenerator)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Map (ArithmeticCircuitTest (..))

data NonInteractiveProofTestData a = TestData a (Witness a)
type PlonkSizeBS = 32
type PlonkBS n = Plonk PlonkSizeBS n BLS12_381_G1 BLS12_381_G2 ByteString

instance (Show a, Show (Input a), Show (Witness a)) =>
    Show (NonInteractiveProofTestData a) where
    show (TestData a w) = "TestData: \n" ++ show a ++ "\n" ++ show w

instance (KZG c1 c2 d ~ kzg, NonInteractiveProof kzg, Arbitrary kzg, Arbitrary (Witness kzg)) =>
    Arbitrary (NonInteractiveProofTestData (KZG c1 c2 d)) where
    arbitrary = TestData <$> arbitrary <*> arbitrary

instance forall n . (KnownNat n) => Arbitrary (NonInteractiveProofTestData (PlonkBS n)) where
    arbitrary = do
        ArithmeticCircuitTest ac wi <- arbitrary :: Gen (ArithmeticCircuitTest (ScalarField BLS12_381_G1) Par1)
        let inputLen = length . inputVariables $ ac
        vecPubInp <- genSubset (value @n) inputLen
        let (omega, k1, k2) = getParams $ value @PlonkSizeBS
        pl <- Plonk omega k1 k2 (Vector vecPubInp) ac <$> arbitrary
        secret <- arbitrary
        return $ TestData pl (PlonkWitnessInput $ witnessGenerator ac wi, secret)
