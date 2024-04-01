module ZkFold.Symbolic.Data.Conditional (
    Conditional (..)
) where

import           Prelude                          hiding (Bool, Num (..), (/))
import qualified Prelude                          as Haskell

import           ZkFold.Base.Algebra.Basic.Field  (Zp)
import           ZkFold.Base.Algebra.Basic.Number (Prime)
import           ZkFold.Symbolic.Data.Bool        (Bool (..), BoolType (..))

class BoolType b => Conditional b a where
    bool :: a -> a -> b -> a

    gif :: b -> a -> a -> a
    gif b x y = bool y x b

    (?) :: b -> a -> a -> a
    (?) = gif

instance Conditional Haskell.Bool a where
    bool f t b = if b then t else f

instance Prime p => Conditional (Bool (Zp p)) x where
    bool f t b = if b == true then t else f
