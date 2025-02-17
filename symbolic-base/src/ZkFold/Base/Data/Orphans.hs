{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Data.Orphans where

import           Control.DeepSeq  (NFData, NFData1)
import           Data.Binary      (Binary)
import           Data.Eq          (Eq)
import           Data.Functor     (Functor)
import           Data.Functor.Rep (Representable (..), WrappedRep (..))
import           Data.Ord         (Ord)
import           GHC.Generics     (Par1, U1, (:*:), (:.:))

instance NFData1 U1
instance NFData1 Par1
instance (NFData1 f, NFData1 g) => NFData1 (f :*: g)
instance (Functor f, NFData1 f, NFData1 g) => NFData1 (f :.: g)

deriving newtype instance Binary (Rep f) => Binary (WrappedRep f)
deriving newtype instance NFData (Rep f) => NFData (WrappedRep f)
deriving instance Eq (Rep f) => Eq (WrappedRep f)
deriving instance Ord (Rep f) => Ord (WrappedRep f)
