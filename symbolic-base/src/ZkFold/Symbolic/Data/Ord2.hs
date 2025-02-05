{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Ord2
  ( IsOrdering (..)
  , Ord (..)
  ) where

import           GHC.Generics
import           Prelude                         (Monoid, Semigroup, type (~), ($), (<$>), fmap)
import qualified Prelude
import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.MonadCircuit    (newAssigned)

class Monoid ordering => IsOrdering ordering where
  lt, eq, gt :: ordering

instance IsOrdering Prelude.Ordering where
  lt = Prelude.LT
  eq = Prelude.EQ
  gt = Prelude.GT

class
  ( Eq a
  , IsOrdering (OrderingOf a)
  ) => Ord a where
  type OrderingOf a
  ordering :: a -> a -> a -> OrderingOf a -> a
  compare :: a -> a -> OrderingOf a
  (<), (<=), (>), (>=) :: a -> a -> BooleanOf a
  default (<)
    :: (Ord (BooleanOf a), OrderingOf (BooleanOf a) ~ OrderingOf a)
    => a -> a -> BooleanOf a
  x < y = ordering true false false (compare x y)
  default (<=)
    :: (Ord (BooleanOf a), OrderingOf (BooleanOf a) ~ OrderingOf a)
    => a -> a -> BooleanOf a
  x <= y = ordering true true false (compare x y)
  default (>)
    :: (Ord (BooleanOf a), OrderingOf (BooleanOf a) ~ OrderingOf a)
    => a -> a -> BooleanOf a
  x > y = ordering false false true (compare x y)
  default (>=)
    :: (Ord (BooleanOf a), OrderingOf (BooleanOf a) ~ OrderingOf a)
    => a -> a -> BooleanOf a
  x >= y = ordering false true true (compare x y)
  max, min :: a -> a -> a
  max x y = ordering y x x (compare x y)
  min x y = ordering x x y (compare x y)

-- instance (Prelude.Ord a, Eq a, BooleanOf a ~ Prelude.Bool) => Ord a where
--   type OrderingOf a = Prelude.Ordering
--   ordering ltCase eqCase gtCase = \case
--     Prelude.LT -> ltCase
--     Prelude.EQ -> eqCase
--     Prelude.GT -> gtCase
--   compare = Prelude.compare
--   (<) = (Prelude.<)
--   (<=) = (Prelude.<=)
--   (>) = (Prelude.>)
--   (>=) = (Prelude.>=)
--   min = Prelude.min
--   max = Prelude.max

newtype Ordering c = Ordering (c Par1)
  deriving (Generic)
instance Symbolic c => Semigroup (Ordering c) where
  Ordering o1 <> Ordering o2 = Ordering $ fromCircuit2F o1 o2 $
    \(Par1 v1) (Par1 v2) -> Par1 <$>
      newAssigned (\x -> let x1 = x v1; x2 = x v2 in x1 * x1 * (x1 - x2) + x2)
instance Symbolic c => Monoid (Ordering c) where
  mempty = eq
instance Symbolic c => IsOrdering (Ordering c) where
  lt = Ordering $ embed (Par1 (negate one))
  eq = Ordering $ embed (Par1 zero)
  gt = Ordering $ embed (Par1 one)

instance Symbolic c => Ord (Bool c) where
  type OrderingOf (Bool c) = Ordering c
  ordering (Bool blt) (Bool beq) (Bool bgt) (Ordering o) =
    Bool $ fromCircuit4F blt beq bgt o $
      \(Par1 vlt) (Par1 veq) (Par1 vgt) (Par1 vord) -> fmap Par1 $
        newAssigned $ \x ->
          let
            xlt = x vlt
            xeq = x veq
            xgt = x vgt
            xord = x vord
            half = fromConstant (one // (one + one) :: BaseField c)
            xIsLT = half * xord * (xord - one)
            xIsGT = half * xord * (xord + one)
            xIsEq = one - xord*xord
          in half * (xIsLT * xlt + xIsEq * xeq + xIsGT * xgt)
  compare (Bool b1) (Bool b2) = Ordering $ fromCircuit2F b1 b2 $
    \(Par1 v1) (Par1 v2) -> fmap Par1 $
      newAssigned $ \x -> let x1 = x v1; x2 = x v2 in x1 - x2
