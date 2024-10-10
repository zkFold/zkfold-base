{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Eq.Structural where

import           Data.Functor.Rep           (Representable)
import           Data.Proxy                 (Proxy (..))
import           Data.Traversable           (Traversable)
import           Prelude                    (type (~))

import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Eq

newtype Structural a = Structural a
-- ^ A newtype wrapper for easy definition of Eq instances.

instance
    ( SymbolicData x
    , Context x ~ c
    , Support x ~ Proxy c
    , Symbolic c
    , Representable (Layout x)
    , Traversable (Layout x)
    ) => Eq (Bool c) (Structural x) where

    Structural x == Structural y =
        let x' = pieces x Proxy
            y' = pieces y Proxy
         in x' == y'

    Structural x /= Structural y =
        let x' = pieces x Proxy
            y' = pieces y Proxy
         in x' /= y'
