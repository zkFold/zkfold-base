{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Compare where

import           Data.Distributive               (Distributive (..))
import           Data.Functor.Rep
import           GHC.Generics                    (Generic1)
import           Numeric.Natural                 (Natural)
import           Prelude                         (Foldable (..), Functor, Integer, Traversable)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Types2          (Symbolic', SymbolicData')

newtype Bool a = Bool a
  deriving stock (Generic1, Functor, Foldable, Traversable)
  deriving anyclass Representable

instance Distributive Bool where
  distribute = distributeRep
  collect = collectRep
deriving via Representably Bool instance
  Field a => VectorSpace a Bool
deriving via Representably Bool a instance
  AdditiveSemigroup a => AdditiveSemigroup (Bool a)
deriving via Representably Bool a instance
  AdditiveMonoid a => AdditiveMonoid (Bool a)
deriving via Representably Bool a instance
  AdditiveGroup a => AdditiveGroup (Bool a)
deriving via Representably Bool a instance
  Scale Natural a => Scale Natural (Bool a)
deriving via Representably Bool a instance
  Scale Integer a => Scale Integer (Bool a)
deriving via Representably Bool a instance
  MultiplicativeMonoid a => Scale a (Bool a)
instance Symbolic' a => Eq a Bool

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

class SymbolicData' a u => Eq a u where
  (==) :: u a -> u a -> Bool a
  u == v = Bool (foldl (*) one (zipWithV equal u v))

(/=) :: Eq a u => u a -> u a -> Bool a
x /= y = not (x == y)

newtype Ordering a = Ordering a
  deriving stock (Generic1, Functor, Foldable, Traversable)
  deriving anyclass Representable

instance Distributive Ordering where
  distribute = distributeRep
  collect = collectRep
deriving via Representably Ordering instance
  Field a => VectorSpace a Ordering
deriving via Representably Ordering a instance
  AdditiveSemigroup a => AdditiveSemigroup (Ordering a)
deriving via Representably Ordering a instance
  AdditiveMonoid a => AdditiveMonoid (Ordering a)
deriving via Representably Ordering a instance
  AdditiveGroup a => AdditiveGroup (Ordering a)
deriving via Representably Ordering a instance
  Scale Natural a => Scale Natural (Ordering a)
deriving via Representably Ordering a instance
  Scale Integer a => Scale Integer (Ordering a)
deriving via Representably Ordering a instance
  MultiplicativeMonoid a => Scale a (Ordering a)
instance Symbolic' a => Eq a Ordering

lt :: Symbolic' a => Ordering a
lt = Ordering (negate one)

eq :: Symbolic' a => Ordering a
eq = Ordering zero

gt :: Symbolic' a => Ordering a
gt = Ordering one

class SymbolicData' a u => Ord a u where
  compare :: u a -> u a -> Ordering a
  compare u v =
    let lexicographical x y = x * x * (x - y) + y
    in Ordering (foldl lexicographical zero (zipWithV trichotomy u v))

(<), (>), (<=), (>=) :: Ord a u => u a -> u a -> Bool a
u < v = compare u v == lt
u > v = compare u v == gt
u <= v = not (u > v)
u >= v = not (u < v)

min, max :: Ord a u => u a -> u a -> u a
min u v = bool u v (u < v)
max u v = bool u v (u > v)
