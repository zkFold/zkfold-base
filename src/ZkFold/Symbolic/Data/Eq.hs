module ZkFold.Symbolic.Data.Eq (
    Eq(..),
    elem
) where

import           Data.Bool                               (bool)
import qualified Data.Eq                                 as Haskell
import           Data.Foldable                           (Foldable)

import           ZkFold.Symbolic.Compiler.Arithmetizable (Arithmetic)
import           ZkFold.Symbolic.Data.Bool               (Bool, BoolType (..), any)
import           ZkFold.Symbolic.Interpreter             (Interpreter)

class Eq b a where
    infix 4 ==
    (==) :: a -> a -> b

    infix 4 /=
    (/=) :: a -> a -> b

elem :: (BoolType b, Eq b a, Foldable t) => a -> t a -> b
elem x = any (== x)

instance Arithmetic a => Eq (Bool (Interpreter a)) (Interpreter a 1) where
    x == y = bool false true (x Haskell.== y)
    x /= y = bool false true (x Haskell./= y)
