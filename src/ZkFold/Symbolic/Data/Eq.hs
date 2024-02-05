{-# LANGUAGE TypeApplications #-}

module ZkFold.Symbolic.Data.Eq (
    Eq(..),
    elem
) where

import           Control.Monad.State                                    (evalState)
import           Data.Bool                                              (bool)
import           Prelude                                                hiding (Bool, Eq (..), Num (..), any, elem, not, product, (/), (/=), (==))
import qualified Prelude                                                as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                        (Zp)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool                              (Bool (..), BoolType (..), all1, any)
import           ZkFold.Symbolic.Data.DiscreteField

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
        in case zs of
            [] -> true
            _  -> all1 (isZero @(Bool (ArithmeticCircuit a)) @(ArithmeticCircuit a)) zs

    x /= y =
        let x' = evalState (arithmetize x) mempty
            y' = evalState (arithmetize y) mempty
            zs = zipWith (-) x' y'
        in case zs of
            [] -> false
            _  -> not $ all1 (isZero @(Bool (ArithmeticCircuit a)) @(ArithmeticCircuit a)) zs

elem :: Eq b a => a -> [a] -> b
elem x = any (== x)
