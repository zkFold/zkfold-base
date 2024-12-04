{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Input where

import           Data.Function                           (($))
import           Data.Functor                            (Functor, (<$>))
import           Data.Functor.Classes                    (Show1)
import           Data.List                               ((++))
import           Test.QuickCheck                         (Arbitrary (..))
import           Text.Show                               (Show, show)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.EllipticCurve.Class (EllipticCurve (..))
import           ZkFold.Symbolic.Compiler                ()

newtype PlonkupInput l c = PlonkupInput { unPlonkupInput :: l (ScalarField c) }

instance (Show1 l, Show (ScalarField c)) => Show (PlonkupInput l c) where
    show (PlonkupInput v) = "Plonkup Input: " ++ show v

instance (Arbitrary (l (ScalarField c))) => Arbitrary (PlonkupInput l c) where
    arbitrary = PlonkupInput <$> arbitrary

plonkupVerifierInput ::
  (Functor l, Field (ScalarField c)) => l (ScalarField c) -> PlonkupInput l c
plonkupVerifierInput input = PlonkupInput $ negate <$> input
