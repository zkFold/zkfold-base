{-# LANGUAGE AllowAmbiguousTypes     #-}
{-# LANGUAGE DerivingStrategies      #-}
{-# LANGUAGE MagicHash               #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module ZkFold.Symbolic.Base.Function
  ( FunctionSpace (..)
  , InputSpace
  , OutputSpace
  ) where

import Control.Category
import Data.Type.Equality

import ZkFold.Symbolic.Base.Vector

{- | `FunctionSpace` class of functions over variables.

The type @FunctionSpace a f => f@ should be equal to some

@vN a -> .. -> v1 a -> v0 a@

which via multiple-uncurrying is equivalent to

@(vN :*: .. :*: v1 :*: U1) a -> v0 a@
-}
class FunctionSpace a f where
  uncurryF :: f -> InputSpace a f a -> OutputSpace a f a
  curryF :: (InputSpace a f a -> OutputSpace a f a) -> f

type family InputSpace a f where
  InputSpace a (x a -> f) = x :*: InputSpace a f
  InputSpace a (y a) = U1

type family OutputSpace a f where
  OutputSpace a (x a -> f) = OutputSpace a f
  OutputSpace a (y a) = y

instance {-# OVERLAPPABLE #-}
  ( OutputSpace a (y a) ~ y
  , InputSpace a (y a) ~ U1
  ) => FunctionSpace a (y a) where
    uncurryF f _ = f
    curryF k = k U1

instance {-# OVERLAPPING #-}
  ( OutputSpace a (x a -> f) ~ OutputSpace a f
  , InputSpace a (x a -> f) ~ x :*: InputSpace a f
  , FunctionSpace a f
  ) => FunctionSpace a (x a -> f) where
    uncurryF f (i :*: j) = uncurryF (f i) j
    curryF k x = curryF (k . (:*:) x)
