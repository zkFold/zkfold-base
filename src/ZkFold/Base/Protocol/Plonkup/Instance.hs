{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Instance where

import           Prelude                                 hiding (Num (..), drop, length, sum, take, (!!), (/), (^))
import           Test.QuickCheck                         (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class (EllipticCurve (..))
import           ZkFold.Base.Data.Vector                 (Vector (..), unsafeToVector)
import           ZkFold.Prelude                          (take)
import           ZkFold.Symbolic.Compiler                ()

newtype PlonkInput l c = PlonkInput { unPlonkInput :: Vector l (ScalarField c) }

instance Show (ScalarField c) => Show (PlonkInput l c) where
    show (PlonkInput v) = "Input: " ++ show v

instance (KnownNat l, Arbitrary (ScalarField c)) => Arbitrary (PlonkInput l c) where
    arbitrary = do
        PlonkInput . unsafeToVector . take (value @l) <$> arbitrary

plonkVerifierInput :: Field (ScalarField c) => Vector l (ScalarField c) -> PlonkInput l c
plonkVerifierInput input = PlonkInput $ fmap negate input
