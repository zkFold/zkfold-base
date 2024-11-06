{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE DerivingStrategies  #-}

module ZkFold.Symbolic.Lookup where

import           Control.DeepSeq  (NFData)
import           Data.Aeson.Types (FromJSON, FromJSONKey, ToJSON, ToJSONKey)
import           GHC.Base         (Eq, Ord)
import           GHC.Generics     (Generic)
import           GHC.Natural      (Natural)
import           GHC.Show         (Show)
import           Prelude          (Maybe (..))


data Lookup = Range Natural
  deriving Generic

deriving anyclass instance FromJSON Lookup
deriving anyclass instance FromJSONKey Lookup
deriving anyclass instance ToJSONKey Lookup
deriving anyclass instance ToJSON Lookup
deriving stock instance Show Lookup
deriving stock instance Eq Lookup
deriving stock instance Ord Lookup
deriving instance NFData Lookup

class HasLookup (l :: Lookup) p where
    rangeLookup :: Lookup -> Maybe Lookup

instance HasLookup (Range n) p where
    rangeLookup l = case l of
        Range r -> Just (Range r)
        _       -> Nothing
