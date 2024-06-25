{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
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

import           Data.Foldable                         (Foldable (..))
import           GHC.Generics
import qualified Prelude                               as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.VectorSpace
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Functor

newtype Ordering a = Ordering a
  deriving stock
    ( Haskell.Functor
    , Haskell.Foldable
    , Haskell.Traversable
    )
deriving via Par1 instance VectorSpace a Ordering
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

instance Ring a => Haskell.Semigroup (Ordering a) where
  Ordering x <> Ordering y = Ordering (x * x * (x - y) + y)
instance Ring a => Haskell.Monoid (Ordering a) where
  mempty = eq

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
            Ordering (foldl lexicographical zero uv)
instance TrichotomyField a => Ord a Bool
instance TrichotomyField a => Ord a Ordering
instance TrichotomyField a => Ord a Par1
instance (Ring a, Ord a u, Ord a v) => Ord a (u :*: v) where
  compare (u1 :*: v1) (u2 :*: v2) = compare u1 u2 Haskell.<> compare v1 v2
instance (Haskell.Applicative v, Foldable v, Ring a, Ord a u) => Ord a (v :.: u) where
  compare fu fv = fold (unComp1 (zipWith compare fu fv))

(<=), (<), (>=), (>) :: (TrichotomyField a, Ord a u) => u a -> u a -> Bool a
u <= v = not (u > v)
u < v = compare u v == lt
u >= v = not (u < v)
u > v = compare u v == gt

max, min :: (TrichotomyField a, Ord a u, VectorSpace a u) => u a -> u a -> u a
max x y = bool y x (x <= y)
min x y = bool y x (x >= y)
