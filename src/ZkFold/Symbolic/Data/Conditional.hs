module ZkFold.Symbolic.Data.Conditional where

import           Prelude                   hiding (Bool, Num (..), (/))

import           ZkFold.Symbolic.Data.Bool (BoolType (..))

class BoolType b => Conditional b a where
    bool :: a -> a -> b -> a

    gif :: b -> a -> a -> a
    gif b x y = bool y x b

    (?) :: b -> a -> a -> a
    (?) = gif

instance {-# OVERLAPPABLE #-} (BoolType b, Eq b) => Conditional b x where
    bool f t b = if b == true then t else f
