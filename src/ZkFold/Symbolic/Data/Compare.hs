{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Compare
  ( Ordering
  , lt
  , eq
  , gt
  , Ord (..)
  , (<=)
  , (<)
  , (>=)
  , (>)
  , min
  , max
  ) where

import           Data.Functor.Identity                 (Identity (..))
import qualified Prelude                               as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.VectorSpace
import           ZkFold.Symbolic.Data.Bool

newtype Ordering a = Ordering a
  deriving stock
    ( Haskell.Functor
    , Haskell.Foldable
    , Haskell.Traversable
    )
deriving via Identity instance VectorSpace a Ordering
instance DiscreteField a => Eq a Ordering
instance (Ring a, Haskell.Eq a) => Haskell.Show (Ordering a) where
    show (Ordering a) =
        if a Haskell.== negate one then "<"
        else if a Haskell.== zero then "="
        else ">"

lt, eq, gt :: Ring a => Ordering a
lt = Ordering (negate one)
eq = Ordering zero
gt = Ordering one

class Eq a u => Ord a u where
    compare :: u a -> u a -> Ordering a
    default compare
      :: (TrichotomyField a, Haskell.Foldable u, VectorSpace a u)
      => u a -> u a -> Ordering a
    compare u v =
        let
            lexicographical x y = x * x * (x - y) + y
            uv = zipWithV trichotomy u v
        in
            Ordering (Haskell.foldl lexicographical zero uv)
instance TrichotomyField a => Ord a Bool
instance TrichotomyField a => Ord a Ordering

(<=), (<), (>=), (>) :: (TrichotomyField a, Ord a u) => u a -> u a -> Bool a
u <= v = not (u > v)
u < v = compare u v == lt
u >= v = not (u < v)
u > v = compare u v == gt

max, min :: (TrichotomyField a, Ord a u, VectorSpace a u) => u a -> u a -> u a
max x y = bool y x (x <= y)
min x y = bool y x (x >= y)
