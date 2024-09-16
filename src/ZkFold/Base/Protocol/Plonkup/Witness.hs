{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Witness where

import           Prelude                                 hiding (Num (..), drop, length, sum, take, (!!), (/), (^))
import           Test.QuickCheck                         (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Number        (KnownNat)
import           ZkFold.Base.Algebra.EllipticCurve.Class (EllipticCurve (..))
import           ZkFold.Base.Data.Vector                 (Vector)

newtype PlonkupWitnessInput i c = PlonkupWitnessInput (Vector i (ScalarField c))

instance Show (ScalarField c) => Show (PlonkupWitnessInput i c) where
    show (PlonkupWitnessInput v) = "Plonkup Witness Input: " ++ show v

instance (KnownNat i, Arbitrary (ScalarField c)) => Arbitrary (PlonkupWitnessInput i c) where
    arbitrary = PlonkupWitnessInput <$> arbitrary
