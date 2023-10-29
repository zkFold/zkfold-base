module ZkFold.Symbolic.Data.Eq (
    Eq(..),
    elem
) where

import           Control.Monad.State             (evalState)
import           Data.Bool                       (bool)
import           Prelude                         hiding (Num(..), Eq(..), Bool, (/=), (==), (/), any, product, elem)
import qualified Prelude                         as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field (Zp)
import           ZkFold.Symbolic.Arithmetization (Arithmetizable (..), ArithmeticCircuit)
import           ZkFold.Symbolic.Data.Bool       (BoolType (..), Bool (..), any)

class BoolType b => Eq b a where
    (==) :: a -> a -> b

    (/=) :: a -> a -> b

instance Haskell.Eq a => Eq Haskell.Bool a where
    x == y = x Haskell.== y
    x /= y = x Haskell./= y

instance (Prime p, Haskell.Eq x) => Eq (Bool (Zp p)) x where
    x == y = Bool $ bool zero one (x Haskell.== y)
    x /= y = Bool $ bool zero one (x Haskell./= y)

instance Arithmetizable a x => Eq (Bool (ArithmeticCircuit a)) x where
    x == y =
        let x' = evalState (arithmetize x) mempty
            y' = evalState (arithmetize y) mempty
            zs = zipWith (-) x' y'
            bs = map (\z -> one - z / z) zs
        in Bool $ product bs

    x /= y =
        let x' = evalState (arithmetize x) mempty
            y' = evalState (arithmetize y) mempty
            zs = zipWith (-) x' y'
            bs = map (\z -> one - z / z) zs
        in Bool $ one - product bs

elem :: Eq b a => a -> [a] -> b
elem x = any (== x)