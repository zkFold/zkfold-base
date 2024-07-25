{-# LANGUAGE TypeOperators #-}

module ZkFold.Base.Control.HApplicative where

import           GHC.Generics              (U1 (..), (:*:) (..))

import           ZkFold.Base.Data.HFunctor (HFunctor)

class HFunctor c => HApplicative c where
  hpure :: (forall a. f a) -> c f
  hliftA2 :: (forall a. f a -> g a -> h a) -> c f -> c g -> c h

hunit :: HApplicative c => c U1
hunit = hpure U1

hpair :: HApplicative c => c f -> c g -> c (f :*: g)
hpair = hliftA2 (:*:)
