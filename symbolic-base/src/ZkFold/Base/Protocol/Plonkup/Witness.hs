{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Witness where

import           Control.Applicative                     ((<*>))
import           Data.Functor                            ((<$>))
import           Data.Functor.Classes                    (Show1)
import           Data.List                               ((++))
import           Test.QuickCheck                         (Arbitrary (..), Arbitrary1, arbitrary1)
import           Text.Show                               (Show, show)

import           ZkFold.Base.Algebra.EllipticCurve.Class (EllipticCurve (..))

data PlonkupWitnessInput p i c = PlonkupWitnessInput
  { payloadInput :: p (ScalarField c)
  , witnessInput :: i (ScalarField c)
  }

instance (Show1 p, Show1 i, Show (ScalarField c))
  => Show (PlonkupWitnessInput p i c) where
    show (PlonkupWitnessInput p v) = "Plonkup Witness Input: " ++ show p ++ ", " ++ show v

instance (Arbitrary1 p, Arbitrary1 i, Arbitrary (ScalarField c))
  => Arbitrary (PlonkupWitnessInput p i c) where
    arbitrary = PlonkupWitnessInput <$> arbitrary1 <*> arbitrary1
