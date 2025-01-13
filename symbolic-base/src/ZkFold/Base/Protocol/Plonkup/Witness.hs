{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Witness where

import           Control.Applicative  ((<*>))
import           Data.Functor         ((<$>))
import           Data.Functor.Classes (Show1)
import           Data.List            ((++))
import           Test.QuickCheck      (Arbitrary (..), Arbitrary1, arbitrary1)
import           Text.Show            (Show, show)

import           ZkFold.Base.Algebra.EllipticCurve.Class    (CyclicGroup (..))

data PlonkupWitnessInput p i g = PlonkupWitnessInput
  { payloadInput :: p (ScalarFieldOf g)
  , witnessInput :: i (ScalarFieldOf g)
  }

instance (Show1 p, Show1 i, Show (ScalarFieldOf g))
  => Show (PlonkupWitnessInput p i g) where
    show (PlonkupWitnessInput p v) = "Plonkup Witness Input: " ++ show p ++ ", " ++ show v

instance (Arbitrary1 p, Arbitrary1 i, Arbitrary (ScalarFieldOf g))
  => Arbitrary (PlonkupWitnessInput p i g) where
    arbitrary = PlonkupWitnessInput <$> arbitrary1 <*> arbitrary1
