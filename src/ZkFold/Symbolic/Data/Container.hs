{-# LANGUAGE TypeOperators #-}
module ZkFold.Symbolic.Data.Container where

import           Data.Functor.Rep
import           GHC.Generics

zipWith :: Representable f => (u a -> v a -> w a) -> (f :.: u) a -> (f :.: v) a -> (f :.: w) a
zipWith f (Comp1 u) (Comp1 v) = Comp1 (mzipWithRep f u v)

zip :: Representable f => (f :.: u) a -> (f :.: v) a -> (f :.: (u :*: v)) a
zip = zipWith (:*:)

replicate :: Representable f => u a -> (f :.: u) a
replicate u = Comp1 (pureRep u)
