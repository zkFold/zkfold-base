{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Witness where

import           Prelude                                 hiding (Num (..), drop, length, sum, take, (!!), (/), (^))
import           Test.QuickCheck                         (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Number        (KnownNat)
import           ZkFold.Base.Algebra.EllipticCurve.Class (EllipticCurve (..))
import           ZkFold.Base.Data.Vector                 (Vector)

data PlonkupWitnessInput p i c = PlonkupWitnessInput
  { payloadInput :: p (ScalarField c)
  , witnessInput :: Vector i (ScalarField c)
  }

instance (Show (ScalarField c), Show (p (ScalarField c)))
  => Show (PlonkupWitnessInput p i c) where
    show (PlonkupWitnessInput p v) = "Plonkup Witness Input: " ++ show p ++ ", " ++ show v

instance (KnownNat i, Arbitrary (ScalarField c), Arbitrary (p (ScalarField c)))
  => Arbitrary (PlonkupWitnessInput p i c) where
    arbitrary = PlonkupWitnessInput <$> arbitrary <*> arbitrary
