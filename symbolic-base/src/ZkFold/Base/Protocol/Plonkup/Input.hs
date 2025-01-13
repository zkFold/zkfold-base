{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Input where

import           Data.Function                           (($))
import           Data.Functor                            (Functor, (<$>))
import           Data.Functor.Classes                    (Show1)
import           Data.List                               ((++))
import           Test.QuickCheck                         (Arbitrary (..))
import           Text.Show                               (Show, show)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Compiler                ()

newtype PlonkupInput l f = PlonkupInput { unPlonkupInput :: l f }

instance (Show1 l, Show f) => Show (PlonkupInput l f) where
    show (PlonkupInput v) = "Plonkup Input: " ++ show v

instance (Arbitrary (l f)) => Arbitrary (PlonkupInput l f) where
    arbitrary = PlonkupInput <$> arbitrary

plonkupVerifierInput ::
  (Functor l, Field f) => l f -> PlonkupInput l f
plonkupVerifierInput input = PlonkupInput $ negate <$> input
