{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Eq (
    Eq(..),
    elem,
    GEq (..)
) where

import           Data.Bool                        (bool)
import           Data.Foldable                    (Foldable)
import           Data.Functor.Rep                 (Representable, mzipRep, mzipWithRep)
import           Data.Traversable                 (Traversable, for)
import qualified Data.Vector                      as V
import qualified GHC.Generics                     as G
import           Prelude                          (return, ($))
import qualified Prelude                          as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Package
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool        (Bool (Bool), BoolType (..), all, any)
import           ZkFold.Symbolic.Data.Combinators (runInvert)
import           ZkFold.Symbolic.MonadCircuit

class Eq b a where
    infix 4 ==
    (==) :: a -> a -> b
    default (==) :: (G.Generic a, GEq b (G.Rep a)) => a -> a -> b
    x == y = geq (G.from x) (G.from y)

    infix 4 /=
    (/=) :: a -> a -> b
    default (/=) :: (G.Generic a, GEq b (G.Rep a)) => a -> a -> b
    x /= y = gneq (G.from x) (G.from y)

elem :: (BoolType b, Eq b a, Foldable t) => a -> t a -> b
elem x = any (== x)

instance Eq Haskell.Bool Natural where
    (==) = (Haskell.==)
    (/=) = (Haskell./=)
instance Eq Haskell.Bool Haskell.Bool where
    (==) = (Haskell.==)
    (/=) = (Haskell./=)
instance Eq Haskell.Bool Haskell.String where
    (==) = (Haskell.==)
    (/=) = (Haskell./=)
instance KnownNat n => Eq Haskell.Bool (Zp n) where
    (==) = (Haskell.==)
    (/=) = (Haskell./=)

instance (Symbolic c, Haskell.Eq (BaseField c), Representable f, Traversable f)
  => Eq (Bool c) (c f) where
    x == y =
        let
            result = symbolic2F x y
                (mzipWithRep (\i j -> bool zero one (i Haskell.== j)))
                (\x' y' -> do
                    difference <- for (mzipRep x' y') $ \(i, j) ->
                        newAssigned (\w -> w i - w j)
                    (isZeros, _) <- runInvert difference
                    return isZeros
                )
        in
            all Bool (unpacked result)

    x /= y =
        let
            result = symbolic2F x y
                (mzipWithRep (\i j -> bool zero one (i Haskell./= j)))
                (\x' y' -> do
                    difference <- for (mzipRep x' y') $ \(i, j) ->
                        newAssigned (\w -> w i - w j)
                    (isZeros, _) <- runInvert difference
                    for isZeros $ \isZ ->
                      newAssigned (\w -> one - w isZ)
                )
        in
            any Bool (unpacked result)

instance (BoolType b, Eq b x) => Eq b (Vector n x) where
    u == v = V.foldl (&&) true (V.zipWith (==) (toV u) (toV v))
    u /= v = V.foldl (||) false (V.zipWith (/=) (toV u) (toV v))

deriving newtype instance Symbolic c => Eq (Bool c) (Bool c)

instance (BoolType b, Eq b x0, Eq b x1) => Eq b (x0,x1)
instance (BoolType b, Eq b x0, Eq b x1, Eq b x2) => Eq b (x0,x1,x2)
instance (BoolType b, Eq b x0, Eq b x1, Eq b x2, Eq b x3) => Eq b (x0,x1,x2,x3)

instance (BoolType bool, Eq bool field) => Eq bool (Ext2 field i)
instance (BoolType bool, Eq bool field) => Eq bool (Ext3 field i)

class GEq b u where
    geq :: u x -> u x -> b
    gneq :: u x -> u x -> b

instance (BoolType b, GEq b u, GEq b v) => GEq b (u G.:*: v) where
    geq (x0 G.:*: x1) (y0 G.:*: y1) = geq x0 y0 && geq x1 y1
    gneq (x0 G.:*: x1) (y0 G.:*: y1) = gneq x0 y0 || gneq x1 y1

instance GEq b v => GEq b (G.M1 i c v) where
    geq (G.M1 x) (G.M1 y) = geq x y
    gneq (G.M1 x) (G.M1 y) = gneq x y

instance Eq b x => GEq b (G.Rec0 x) where
    geq (G.K1 x) (G.K1 y) = x == y
    gneq (G.K1 x) (G.K1 y) = x /= y
