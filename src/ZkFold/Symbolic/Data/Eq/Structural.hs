{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Eq.Structural where

import           Prelude                    (type (~))

import           ZkFold.Base.Data.Vector    (Vector)
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Eq

newtype Structural a = Structural a
-- ^ A newtype wrapper for easy definition of Eq instances.

instance
    ( SymbolicData c x
    , Support c x ~ ()
    , n ~ TypeSize c x
    , Eq (Bool c) (c (Vector n))
    ) => Eq (Bool c) (Structural x) where

    Structural x == Structural y =
        let x' = pieces @c x ()
            y' = pieces y ()
         in x' == y'

    Structural x /= Structural y =
        let x' = pieces @c x ()
            y' = pieces y ()
         in x' /= y'
