module ZkFold.Symbolic.Data.Eq (
    Eq(..),
    elem
) where

import           Data.Bool                        (bool)
import qualified Data.Eq                          as Haskell
import           Data.Foldable                    (Foldable)

import           ZkFold.Base.Algebra.Basic.Field  (Zp)
import           ZkFold.Base.Algebra.Basic.Number (KnownNat)
import           ZkFold.Symbolic.Data.Bool        (Bool, BoolType (..), any)

class BoolType b => Eq b a where
    infix 4 ==
    (==) :: a -> a -> b

    infix 4 /=
    (/=) :: a -> a -> b

elem :: (Eq b a, Foldable t) => a -> t a -> b
elem x = any (== x)

instance KnownNat p => Eq (Bool (Zp p)) (Zp p) where
    x == y = bool false true (x Haskell.== y)
    x /= y = bool false true (x Haskell./= y)
