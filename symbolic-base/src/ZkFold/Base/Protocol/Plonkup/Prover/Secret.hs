{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Plonkup.Prover.Secret where

import           Data.Aeson.Types                            (FromJSON (..), ToJSON (..))
import           GHC.Generics                                (Generic)
import           Prelude                                     hiding (Num (..), drop, length, sum, take, (!!), (/), (^))
import           Test.QuickCheck                             (Arbitrary (..))

import qualified ZkFold.Base.Algebra.EllipticCurve.BLS12_381 as BLS12_381 (Fr)
import           ZkFold.Base.Data.Vector                     (Vector (..))

newtype PlonkupProverSecret scalarField = PlonkupProverSecret (Vector 19 scalarField)
    deriving stock Generic

deriving anyclass instance ToJSON   (PlonkupProverSecret BLS12_381.Fr)
deriving anyclass instance FromJSON (PlonkupProverSecret BLS12_381.Fr)

instance Show scalarField => Show (PlonkupProverSecret scalarField) where
    show (PlonkupProverSecret v) =
        "PlonkupProverSecret: " ++ show v

instance Arbitrary scalarField => Arbitrary (PlonkupProverSecret scalarField) where
    arbitrary = PlonkupProverSecret <$> arbitrary
