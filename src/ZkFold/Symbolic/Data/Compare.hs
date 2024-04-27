{-# LANGUAGE DeriveAnyClass, UndecidableInstances #-}

module ZkFold.Symbolic.Data.Compare where

import           Data.Distributive               (Distributive (..))
import           Data.Functor.Rep
import           GHC.Generics                    (Generic1)
import           Numeric.Natural                 (Natural)
import           Prelude                         (Functor, Foldable (..), Traversable, Integer, undefined)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Types           (Symbolic', SymbolicData')

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

-- structural equality
(===) :: (SymbolicData' a u, Foldable u) => u a -> u a -> Bool a
a === b = Bool (foldl (*) one (zipWithV diEq a b))

newtype Ordering a = Ordering a

le :: Symbolic' a => Ordering a
le = Ordering (negate one)

eq :: Symbolic' a => Ordering a
eq = Ordering zero

ge :: Symbolic' a => Ordering a
ge = Ordering one

-- lexicographical ordering ???
compare
  :: (SymbolicData' a u, Foldable u)
  => u a -> u a -> Ordering a
compare = undefined
  -- as bs =
    -- let cs = zipWithV trichotomy as bs
    -- in Ordering (foldl triMin zero cs)

(<=), (>=), (<), (>)
  :: (SymbolicData' a u, Foldable u)
  => u a -> u a -> Bool a
(<=) = undefined
(>=) = undefined
(<) = undefined
(>) = undefined

min, max
  :: (SymbolicData' a u, Foldable u)
  => u a -> u a -> u a
min = undefined
max = undefined
