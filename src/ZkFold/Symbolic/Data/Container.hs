{-# LANGUAGE TypeOperators #-}
module ZkFold.Symbolic.Data.Container where

import           Data.Functor.Rep
import           GHC.Generics
import qualified Prelude                               as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.VectorSpace

zipWith :: Representable f => (u a -> v a -> w a) -> (f :.: u) a -> (f :.: v) a -> (f :.: w) a
zipWith f (Comp1 u) (Comp1 v) = Comp1 (mzipWithRep f u v)

zip :: Representable f => (f :.: u) a -> (f :.: v) a -> (f :.: (u :*: v)) a
zip = zipWith (:*:)

replicate :: Representable f => u a -> (f :.: u) a
replicate u = Comp1 (pureRep u)

class Functor f where
  fmap :: (u a -> v a) -> f u a -> f v a
instance Haskell.Functor f => Functor ((:.:) f) where
  fmap g (Comp1 f) = Comp1 (Haskell.fmap g f)

class Functor f => Applicative f where
  return :: Ring a => u a -> f u a
  liftA2 :: Ring a => (u a -> v a -> w a) -> f u a -> f v a -> f w a
instance Haskell.Applicative f => Applicative ((:.:) f) where
  return u = Comp1 (Haskell.pure u)
  liftA2 uvw (Comp1 u) (Comp1 v) = Comp1 (Haskell.liftA2 uvw u v)

class Applicative f => Monad f where
  (>>=) :: (Ring a, VectorSpace a v) => f u a -> (u a -> f v a) -> f v a
instance Haskell.Monad f => Monad ((:.:) f) where
  Comp1 u >>= ufv = Comp1 (u Haskell.>>= unComp1 Haskell.. ufv)
