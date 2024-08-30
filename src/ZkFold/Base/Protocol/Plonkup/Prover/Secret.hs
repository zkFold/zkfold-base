{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Prover.Secret where

import           GHC.Generics                                        (Generic)
import           Prelude                                             hiding (Num (..), drop, length, sum, take, (!!),
                                                                      (/), (^))
import           Test.QuickCheck                                     (Arbitrary (..))

import           ZkFold.Base.Algebra.EllipticCurve.Class             (EllipticCurve (..))

data PlonkProverSecret c = PlonkProverSecret {
        b1  :: ScalarField c,
        b2  :: ScalarField c,
        b3  :: ScalarField c,
        b4  :: ScalarField c,
        b5  :: ScalarField c,
        b6  :: ScalarField c,
        b7  :: ScalarField c,
        b8  :: ScalarField c,
        b9  :: ScalarField c,
        b10 :: ScalarField c,
        b11 :: ScalarField c,
        b12 :: ScalarField c,
        b13 :: ScalarField c,
        b14 :: ScalarField c,
        b15 :: ScalarField c,
        b16 :: ScalarField c,
        b17 :: ScalarField c,
        b18 :: ScalarField c,
        b19 :: ScalarField c
    } deriving Generic

instance Show (ScalarField c) => Show (PlonkProverSecret c) where
    show (PlonkProverSecret b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19) =
        "Prover Secret: "
        ++ show b1 ++ " "
        ++ show b2 ++ " "
        ++ show b3 ++ " "
        ++ show b4 ++ " "
        ++ show b5 ++ " "
        ++ show b6 ++ " "
        ++ show b7 ++ " "
        ++ show b8 ++ " "
        ++ show b9 ++ " "
        ++ show b10 ++ " "
        ++ show b11 ++ " "
        ++ show b12 ++ " "
        ++ show b13 ++ " "
        ++ show b14 ++ " "
        ++ show b15 ++ " "
        ++ show b16 ++ " "
        ++ show b17 ++ " "
        ++ show b18 ++ " "
        ++ show b19

instance Arbitrary (ScalarField c) => Arbitrary (PlonkProverSecret c) where
    arbitrary = PlonkProverSecret <$>
        arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
        <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
        <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
        <*> arbitrary <*> arbitrary <*> arbitrary
