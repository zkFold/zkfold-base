{-# LANGUAGE TypeOperators #-}

module ZkFold.Base.Data.Package where

import           Data.Foldable             (Foldable)
import           Data.Function             ((.))
import           Data.Functor              (Functor (..))
import           GHC.Generics              (Par1 (..), (:.:) (..))

import           ZkFold.Base.Data.HFunctor (HFunctor (..))

class HFunctor c => Package c where
  {-# MINIMAL (unpack | unpackWith), (pack | packWith) #-}

  unpack :: Functor f => c (f :.: g) -> f (c g)
  unpack = unpackWith unComp1

  unpackWith :: Functor f => (forall a. h a -> f (g a)) -> c h -> f (c g)
  unpackWith f = unpack . hmap (Comp1 . f)

  pack :: (Foldable f, Functor f) => f (c g) -> c (f :.: g)
  pack = packWith Comp1

  packWith :: (Foldable f, Functor f) => (forall a. f (g a) -> h a) -> f (c g) -> c h
  packWith f = hmap (f . unComp1) . pack

unpacked :: (Package c, Functor f) => c f -> f (c Par1)
unpacked = unpackWith (fmap Par1)

packed :: (Package c, Foldable f, Functor f) => f (c Par1) -> c f
packed = packWith (fmap unPar1)
