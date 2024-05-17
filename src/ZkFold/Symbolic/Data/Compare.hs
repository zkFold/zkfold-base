{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Compare
  ( Eq (..)
  , (/=)
  , Ordering (..)
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
import           ZkFold.Symbolic.Types                 (Symbolic)

class (VectorSpace a u, Haskell.Foldable u) => Eq a u where
    infix 4 ==
    (==) :: Symbolic a => u a -> u a -> Bool a
    u == v = Bool (Haskell.foldl (*) one (zipWithV equal u v))
instance Eq a Bool
instance Eq a Ordering

infix 4 /=
(/=) :: (Symbolic a, Eq a u) => u a -> u a -> Bool a
u /= b = not (u == b)

-- TODO: Don't export constructor
newtype Ordering a = Ordering a
  deriving stock Haskell.Foldable
deriving via Identity instance VectorSpace a Ordering
instance (Symbolic a, Haskell.Eq a) => Haskell.Show (Ordering a) where
    show (Ordering a) =
        if a Haskell.== negate one then "<"
        else if a Haskell.== zero then "="
        else ">"

lt, eq, gt :: Symbolic a => Ordering a
lt = Ordering (negate one)
eq = Ordering zero
gt = Ordering one

class Eq a u => Ord a u where
    compare :: Symbolic a => u a -> u a -> Ordering a
    compare u v =
        let
            lexicographical x y = x * x * (x - y) + y
            uv = zipWithV trichotomy u v
        in
            Ordering (Haskell.foldl lexicographical zero uv)
instance Ord a Bool
instance Ord a Ordering

(<=), (<), (>=), (>) :: (Symbolic a, Ord a u) => u a -> u a -> Bool a
u <= v = not (u > v)
u < v = compare u v == lt
u >= v = not (u < v)
u > v = compare u v == gt

max, min :: (Symbolic a, Ord a u) => u a -> u a -> u a
max x y = bool y x (x <= y)
min x y = bool y x (x >= y)
