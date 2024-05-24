{-# LANGUAGE TypeOperators #-}
module ZkFold.Symbolic.Data.Container where

import Data.Foldable
import Data.Functor.Rep
import GHC.Generics
import ZkFold.Symbolic.Data.Bool
import ZkFold.Base.Algebra.Basic.Class

all :: (Foldable f, Ring a) => (u a -> Bool a) -> (f :.: u) a -> Bool a
all condition (Comp1 xs) = foldl (\b x -> b && condition x) true xs

any :: (Foldable f, Ring a) => (u a -> Bool a) -> (f :.: u) a -> Bool a
any condition (Comp1 xs) = foldl (\b x -> b || condition x) false xs

zap :: Representable f => (f :.: u) a -> (f :.: v) a -> (f :.: (u :*: v)) a
zap (Comp1 u) (Comp1 v) = Comp1 (mzipWithRep (:*:) u v)

replicate :: Representable f => u a -> (f :.: u) a
replicate u = Comp1 (pureRep u)
