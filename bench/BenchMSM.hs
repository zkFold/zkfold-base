{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Main where

import qualified Data.ByteString                                as BS
import qualified Data.Vector                                    as V
import           GHC.Generics                                   (Par1)
import           GHC.TypeNats                                   (KnownNat)
import           Prelude                                        hiding (length, sum, (-))
import           Test.QuickCheck                                (Arbitrary (arbitrary), Gen, generate)
import           Test.Tasty.Bench

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number               (value)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381    (BLS12_381_G1, BLS12_381_G2)
import           ZkFold.Base.Algebra.EllipticCurve.Class        (EllipticCurve (..))
import           ZkFold.Base.Algebra.Polynomials.Univariate     (fromPolyVec)
import           ZkFold.Base.Data.Vector                        hiding (generate)
import           ZkFold.Base.Protocol.ARK.Plonk                 (Plonk (Plonk), PlonkWitnessInput (..), genSubset,
                                                                 getParams)
import           ZkFold.Base.Protocol.Commitment.KZG            (CoreFunction (com'), HaskellCore, KZG)
import           ZkFold.Base.Protocol.NonInteractiveProof       (NonInteractiveProof (..))
import           ZkFold.Prelude                                 (length)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Map (ArithmeticCircuitTest (..))

data NonInteractiveProofTestData a = TestData a (Witness a)
type PlonkSizeBS = 32
type PlonkBS n = Plonk PlonkSizeBS n BLS12_381_G1 BLS12_381_G2 BS.ByteString HaskellCore

instance (Show a, Show (Input a), Show (Witness a)) =>
    Show (NonInteractiveProofTestData a) where
    show (TestData a w) = "TestData: \n" ++ show a ++ "\n" ++ show w

instance (KZG c1 c2 d core ~ kzg, NonInteractiveProof kzg, Arbitrary kzg, Arbitrary (Witness kzg)) =>
    Arbitrary (NonInteractiveProofTestData (KZG c1 c2 d core)) where
    arbitrary = TestData <$> arbitrary <*> arbitrary

instance forall n . (KnownNat n) => Arbitrary (NonInteractiveProofTestData (PlonkBS n)) where
    arbitrary = do
        ArithmeticCircuitTest ac wi <- arbitrary :: Gen (ArithmeticCircuitTest (ScalarField BLS12_381_G1) Par1)
        let inputLen = length . acInput $ ac
        vecPubInp <- genSubset (value @n) inputLen
        let (omega, k1, k2) = getParams $ value @PlonkSizeBS
        pl <- Plonk omega k1 k2 (Vector vecPubInp) ac <$> arbitrary
        secret <- arbitrary
        return $ TestData pl (PlonkWitnessInput $ witnessGenerator ac wi, secret)

propNonInteractiveProof :: forall a .
    NonInteractiveProof a =>
    NonInteractiveProofTestData a -> Bool
propNonInteractiveProof (TestData a w) =
    let sp = setupProve a
        sv = setupVerify a
        (i, p) = prove @a sp w
    in verify @a sv i p

main :: IO ()
main = do
    testData <- generate arbitrary
    defaultMain [ bgroup "MSM group" [ bench "Haskell wrapper" $ nf (propNonInteractiveProof @(PlonkBS 2)) testData ] ]
