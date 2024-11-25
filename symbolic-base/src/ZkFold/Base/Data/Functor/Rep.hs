{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Data.Functor.Rep where

import           Data.Binary      (Binary)
import           Data.Functor.Rep (Rep, WrappedRep (..))

deriving newtype instance Binary (Rep f) => Binary (WrappedRep f)
