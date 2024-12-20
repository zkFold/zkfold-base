{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Data.Orphans where

import           Control.DeepSeq  (NFData)
import           Data.Binary      (Binary)
import           Data.Functor.Rep (Representable (..), WrappedRep (..))
import           Prelude          (Eq, Ord)

deriving newtype instance NFData (Rep f) => NFData (WrappedRep f)
deriving newtype instance Binary (Rep f) => Binary (WrappedRep f)
deriving instance Eq (Rep f) => Eq (WrappedRep f)
deriving instance Ord (Rep f) => Ord (WrappedRep f)
