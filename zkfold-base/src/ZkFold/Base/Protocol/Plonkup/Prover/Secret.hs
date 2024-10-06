{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Prover.Secret where

import           GHC.Generics                            (Generic)
import           Prelude                                 hiding (Num (..), drop, length, sum, take, (!!), (/), (^))
import           Test.QuickCheck                         (Arbitrary (..))

import           ZkFold.Base.Algebra.EllipticCurve.Class (EllipticCurve (..))
import           ZkFold.Base.Data.Vector                 (Vector)

newtype PlonkupProverSecret c = PlonkupProverSecret (Vector 19 (ScalarField c))
    deriving Generic

instance Show (ScalarField c) => Show (PlonkupProverSecret c) where
    show (PlonkupProverSecret v) =
        "PlonkupProverSecret: " ++ show v

instance Arbitrary (ScalarField c) => Arbitrary (PlonkupProverSecret c) where
    arbitrary = PlonkupProverSecret <$> arbitrary
