{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Input where

import           Prelude                                 hiding (Num (..), drop, length, sum, take, (!!), (/), (^))
import           Test.QuickCheck                         (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class (EllipticCurve (..))
import           ZkFold.Base.Data.Vector                 (Vector (..), unsafeToVector)
import           ZkFold.Prelude                          (take)
import           ZkFold.Symbolic.Compiler                ()

newtype PlonkupInput l c = PlonkupInput { unPlonkupInput :: Vector l (ScalarField c) }

instance Show (ScalarField c) => Show (PlonkupInput l c) where
    show (PlonkupInput v) = "Input: " ++ show v

instance (KnownNat l, Arbitrary (ScalarField c)) => Arbitrary (PlonkupInput l c) where
    arbitrary = do
        PlonkupInput . unsafeToVector . take (value @l) <$> arbitrary

plonkupVerifierInput :: Field (ScalarField c) => Vector l (ScalarField c) -> PlonkupInput l c
plonkupVerifierInput input = PlonkupInput $ fmap negate input
