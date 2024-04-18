module ZkFold.Symbolic.Data.Eq (
    Eq(..),
    elem
) where

import           Data.Bool                 (bool)
import           Data.Foldable             (Foldable)
import qualified Prelude                   as Haskell

import           ZkFold.Symbolic.Data.Bool (BoolType (..), any)

class BoolType b => Eq b a where
    (==) :: a -> a -> b
    (/=) :: a -> a -> b

instance {-# OVERLAPPABLE #-} (BoolType b, Haskell.Eq x) => Eq b x where
    x == y = bool false true (x Haskell.== y)
    x /= y = bool false true (x Haskell./= y)

elem :: (Eq b a, Foldable t) => a -> t a -> b
elem x = any (== x)
