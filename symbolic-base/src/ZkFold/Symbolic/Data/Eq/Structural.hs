{-# LANGUAGE TypeOperators #-}

module ZkFold.Symbolic.Data.Eq.Structural where

import           Data.Proxy                 (Proxy (..))
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
    ) => Eq (Bool c) (Structural x) where

    Structural x == Structural y =
        let x' = pieces x Proxy
            y' = pieces y Proxy
         in x' == y'

    Structural x /= Structural y =
        let x' = pieces x Proxy
            y' = pieces y Proxy
         in x' /= y'
