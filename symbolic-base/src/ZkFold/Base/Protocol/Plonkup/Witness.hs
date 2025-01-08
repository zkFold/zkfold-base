{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Witness where

import           Control.Applicative                     ((<*>))
import           Data.Functor                            ((<$>))
import           Data.Functor.Classes                    (Show1)
import           Data.List                               ((++))
import           Test.QuickCheck                         (Arbitrary (..), Arbitrary1, arbitrary1)
import           Text.Show                               (Show, show)

data PlonkupWitnessInput p i scalarField = PlonkupWitnessInput
  { payloadInput :: p scalarField
  , witnessInput :: i scalarField
  }

instance (Show1 p, Show1 i, Show scalarField)
  => Show (PlonkupWitnessInput p i scalarField) where
    show (PlonkupWitnessInput p v) = "Plonkup Witness Input: " ++ show p ++ ", " ++ show v

instance (Arbitrary1 p, Arbitrary1 i, Arbitrary scalarField)
  => Arbitrary (PlonkupWitnessInput p i scalarField) where
    arbitrary = PlonkupWitnessInput <$> arbitrary1 <*> arbitrary1
