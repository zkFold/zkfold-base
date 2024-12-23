{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Prover.Secret where

import           Data.Aeson.Types                            (FromJSON (..), ToJSON (..))
import           GHC.Generics                                (Generic)
import           Prelude                                     hiding (Num (..), drop, length, sum, take, (!!), (/), (^))
import           Test.QuickCheck                             (Arbitrary (..))

import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_G1)
import           ZkFold.Base.Algebra.EllipticCurve.Class     (EllipticCurve (..))
import           ZkFold.Base.Data.Vector                     (Vector (..))

newtype PlonkupProverSecret c = PlonkupProverSecret (Vector 19 (ScalarField c))
    deriving stock Generic

deriving anyclass instance ToJSON   (PlonkupProverSecret BLS12_381_G1)
deriving anyclass instance FromJSON (PlonkupProverSecret BLS12_381_G1)

instance Show (ScalarField c) => Show (PlonkupProverSecret c) where
    show (PlonkupProverSecret v) =
        "PlonkupProverSecret: " ++ show v

instance Arbitrary (ScalarField c) => Arbitrary (PlonkupProverSecret c) where
    arbitrary = PlonkupProverSecret <$> arbitrary
