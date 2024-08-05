{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Eq (
    Eq(..),
    elem
) where

import           Data.Bool                    (bool)
import qualified Data.Eq                      as Haskell
import           Data.Foldable                (Foldable)
import           Data.Traversable             (Traversable, for)
import           Prelude                      (($), (.), return)
import qualified Data.Zip                                                  as Z

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Package
import           ZkFold.Symbolic.Data.Bool    (Bool(Bool), BoolType (..), all, any)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.MonadCircuit

class Eq b a where
    infix 4 ==
    (==) :: a -> a -> b

    infix 4 /=
    (/=) :: a -> a -> b

elem :: (BoolType b, Eq b a, Foldable t) => a -> t a -> b
elem x = any (== x)

instance (Symbolic c, Haskell.Eq (BaseField c), Z.Zip f, Traversable f)
  => Eq (Bool c) (c f) where
    x == y =
        let
            result = symbolic2F x y
                (\x' y' -> Z.zipWith (\i j -> bool zero one (i Haskell.== j)) x' y')
                (\x' y' -> do
                    difference <- for (Z.zip x' y') $ \(i, j) ->
                        newAssigned (\w -> w i - w j)
                    (isZeros, _) <- runInvert difference
                    return isZeros
                )
        in
            all Bool (unpacked result)

    x /= y =
        let
            result = symbolic2F x y
                (\x' y' -> Z.zipWith (\i j -> bool zero one (i Haskell./= j)) x' y')
                (\x' y' -> do
                    difference <- for (Z.zip x' y') $ \(i, j) ->
                        newAssigned (\w -> w i - w j)
                    (isZeros, _) <- runInvert difference
                    notIsZeros <- for isZeros $ \isZ ->
                      newAssigned (\w -> one - w isZ)
                    return notIsZeros
                )
        in
            any Bool (unpacked result)

runInvert :: (MonadCircuit i a m, Z.Zip f, Traversable f) => f i -> m (f i, f i)
runInvert is = do
    js <- for is $ \i -> newConstrained (\x j -> x i * x j) (\x -> let xi = x i in one - xi // xi)
    ks <- for (Z.zip is js) $ \(i, j) -> newConstrained (\x k -> x i * x k + x j - one) (finv . ($ i))
    return (js, ks)
