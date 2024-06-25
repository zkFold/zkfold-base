{-# LANGUAGE TypeOperators #-}
module ZkFold.Symbolic.Data.Functor
  ( Functor (..)
  , Applicative (..)
  , zip
  , (>>)
  , Monad (..)
  ) where

import           Data.Functor.Rep
import           GHC.Generics                          hiding (Rep)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.VectorSpace

class Functor f where
  fmap :: (u a -> v a) -> f u a -> f v a
instance Representable v => Functor ((:.:) v) where
  fmap g (Comp1 v) = Comp1 (fmapRep g v)

class Functor f => Applicative f where
  return :: Ring a => u a -> f u a
  zipWith :: Ring a => (u a -> v a -> w a) -> f u a -> f v a -> f w a
instance Representable v => Applicative ((:.:) v) where
  return u = Comp1 (pureRep u)
  zipWith uvw (Comp1 u) (Comp1 v) = Comp1 (mzipWithRep uvw u v)

zip :: (Ring a, Applicative f) => f u a -> f v a -> f (u :*: v) a
zip = zipWith (:*:)

(>>) :: (Ring a, Applicative f) => f u a -> f v a -> f v a
(>>) = zipWith (\_u v -> v)

class Applicative f => Monad f where
  (>>=) :: (Ring a, VectorSpace a v) => f u a -> (u a -> f v a) -> f v a
