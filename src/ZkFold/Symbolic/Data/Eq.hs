module ZkFold.Symbolic.Data.Eq (
    Eq(..),
    elem
) where

import           Data.Bool                                              (bool)
import           Prelude                                                hiding (Bool, Eq (..), Num (..), any, elem, not, product, (/), (/=), (==))
import qualified Prelude                                                as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                        (Zp)
import           ZkFold.Symbolic.Data.Bool                              (Bool (..), BoolType (..), any)

class BoolType b => Eq b a where
    (==) :: a -> a -> b

    (/=) :: a -> a -> b

instance Haskell.Eq a => Eq Haskell.Bool a where
    x == y = x Haskell.== y
    x /= y = x Haskell./= y

instance (Prime p, Haskell.Eq x) => Eq (Bool (Zp p)) x where
    x == y = Bool $ bool zero one (x Haskell.== y)
    x /= y = Bool $ bool zero one (x Haskell./= y)

elem :: Eq b a => a -> [a] -> b
elem x = any (== x)
