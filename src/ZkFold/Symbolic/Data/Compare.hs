{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Compare where

import           Data.Distributive               (Distributive (..))
import           Data.Functor.Rep
import           GHC.Generics                    (Generic1)
import           Numeric.Natural                 (Natural)
import           Prelude                         (Foldable (..), Functor, Integer, Traversable)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Types           (Symbolic', SymbolicData')

newtype Bool a = Bool a
  deriving stock (Generic1, Functor, Foldable, Traversable)
  deriving anyclass Representable
instance Distributive Bool where
  distribute = distributeRep
  collect = collectRep
deriving via Representably Bool instance Field a => VectorSpace a Bool
deriving via Representably Bool a instance Field a => AdditiveSemigroup (Bool a)
deriving via Representably Bool a instance Field a => AdditiveMonoid (Bool a)
deriving via Representably Bool a instance Field a => AdditiveGroup (Bool a)
deriving via Representably Bool a instance Field a => Scale Natural (Bool a)
deriving via Representably Bool a instance Field a => Scale Integer (Bool a)
deriving via Representably Bool a instance Field a => Scale a (Bool a)
deriving via Linearly Bool instance DiscreteField' a => Eq a Bool
-- deriving via Linearly Bool instance Trichotomy a => Ord a Bool

false :: Symbolic' a => Bool a
false = Bool zero

true :: Symbolic' a => Bool a
true = Bool one

not :: Symbolic' a => Bool a -> Bool a
not (Bool a) = Bool (one - a)

(&&) :: Symbolic' a => Bool a -> Bool a -> Bool a
(&&) (Bool b1) (Bool b2) = Bool (b1 * b2)

(||) :: Symbolic' a => Bool a -> Bool a -> Bool a
(||) (Bool b1) (Bool b2) = Bool (b1 + b2 - b1 * b2)

xor :: Symbolic' a => Bool a -> Bool a -> Bool a
xor (Bool b1) (Bool b2) = Bool (b1 + b2 - scale (2 :: Natural) (b1 * b2))

bool :: SymbolicData' a u => u a -> u a -> Bool a -> u a
bool f t (Bool b) = scale b (t - f) + f

ifThenElse, (?) :: SymbolicData' a u => Bool a -> u a -> u a -> u a
ifThenElse b t f = bool f t b
(?) = ifThenElse

class Eq a u where
  (==) :: u a -> u a -> Bool a
  (/=) :: u a -> u a -> Bool a

-- structural equality
instance (DiscreteField' a, VectorSpace a u, Foldable u)
  => Eq a (Linearly u) where
    Linearly a == Linearly b = Bool (foldl (*) one (zipWithV diEq a b))
    Linearly a /= Linearly b = Bool (one - foldl (*) one (zipWithV diEq a b))

newtype Ordering a = Ordering a

le :: Symbolic' a => Ordering a
le = Ordering (negate one)

eq :: Symbolic' a => Ordering a
eq = Ordering zero

ge :: Symbolic' a => Ordering a
ge = Ordering one

class Ord a u where
  compare :: u a -> u a -> Ordering a
  (<=) :: u a -> u a -> Bool a
  (>=) :: u a -> u a -> Bool a
  (<) :: u a -> u a -> Bool a
  (>) :: u a -> u a -> Bool a
  min :: u a -> u a -> u a
  max :: u a -> u a -> u a
