{-# LANGUAGE TypeOperators #-}
module ZkFold.Symbolic.Data.Functor
  ( Functor (..)
  , Applicative (..)
  , (>>)
  , Monad (..)
  , zip
  , (:*:) (..)
  ) where

import           GHC.Generics                          hiding (Rep)
import qualified Prelude

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.VectorSpace

class Functor f where
  map :: (u a -> v a) -> f u a -> f v a
instance Prelude.Functor v => Functor ((:.:) v) where
  map g (Comp1 v) = Comp1 (Prelude.fmap g v)

class Functor f => Applicative f where
  return :: Ring a => u a -> f u a
  zipWith :: Ring a => (u a -> v a -> w a) -> f u a -> f v a -> f w a
instance Prelude.Applicative v => Applicative ((:.:) v) where
  return u = Comp1 (Prelude.pure u)
  zipWith uvw (Comp1 u) (Comp1 v) = Comp1 (Prelude.liftA2 uvw u v)

(>>) :: (Ring a, Applicative f) => f u a -> f v a -> f v a
(>>) = zipWith (\_u v -> v)

-- | To use @Symbolic.do@ notation,
--
-- >> import qualified ZkFold.Symbolic.Data.Functor as Symbolic
class Applicative f => Monad f where
  (>>=) :: (Ring a, VectorSpace a v) => f u a -> (u a -> f v a) -> f v a

zip :: (Ring a, Applicative f) => f u a -> f v a -> f (u :*: v) a
zip = zipWith (:*:)
