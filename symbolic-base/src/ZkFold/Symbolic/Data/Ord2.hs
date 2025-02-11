{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Data.Ord2
  ( IsOrdering (..)
  , Ord (..)
  , GOrd (..)
  ) where

import           Control.DeepSeq                  (NFData)
import           Data.Foldable                    (foldr)
import           Data.Functor.Rep                 (mzipWithRep)
import           GHC.Generics
import           Prelude                          (Monoid, Semigroup, Show, fmap, type (~), ($), (.), (<$>), (<>))
import qualified Prelude

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Package
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.MonadCircuit     (newAssigned)

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
  type OrderingOf a = GOrderingOf (Rep a)

  ordering :: a -> a -> a -> OrderingOf a -> a
  default ordering
    :: (Generic a, GOrd (Rep a), OrderingOf a ~ GOrderingOf (Rep a))
    => a -> a -> a -> OrderingOf a -> a
  ordering ltCase eqCase gtCase o =
    to (gordering (from ltCase) (from eqCase) (from gtCase) o)

  compare :: a -> a -> OrderingOf a
  default compare
    :: (Generic a, GOrd (Rep a), OrderingOf a ~ GOrderingOf (Rep a))
    => a -> a -> OrderingOf a
  compare x y = gcompare (from x) (from y)

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
deriving instance NFData (c Par1) => NFData (Ordering c)
deriving instance Show (c Par1) => Show (Ordering c)
deriving newtype instance Symbolic c => Conditional (Bool c) (Ordering c)
deriving newtype instance Symbolic c => Eq (Ordering c)
instance Symbolic c => SymbolicData (Ordering c)
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

instance (Symbolic c, LayoutFunctor f)
  => Ord (c f) where
    type OrderingOf (c f) = Ordering c
    ordering x y z (Ordering o) = restore $ \s ->
      ( symbolic4F o (arithmetize x s) (arithmetize y s) (arithmetize z s)
          ( \(Par1 c) l e g ->
              if c Prelude.== negate one then l
              else if c Prelude.== zero then e else g
          )
          Prelude.undefined
      , Prelude.undefined
      )
    compare x y =
        let
            result = symbolic2F x y
                ( mzipWithRep $ \i j -> case Prelude.compare i j of
                    Prelude.LT -> negate one
                    Prelude.EQ -> zero
                    Prelude.GT -> one
                )
                (\x' y' -> do
                    Prelude.undefined
                )
        in
          foldr ((<>) . Ordering) eq (unpacked result)

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

class
  ( GEq u
  , IsOrdering (GOrderingOf u)
  ) => GOrd u where
  type GOrderingOf u
  gordering :: u x -> u x -> u x -> GOrderingOf u -> u x
  gcompare :: u x -> u x -> GOrderingOf u

instance
  ( GOrd u
  , GOrd v
  , GBooleanOf u ~ GBooleanOf v
  , GOrderingOf u ~ GOrderingOf v
  ) => GOrd (u :*: v) where
  type GOrderingOf (u :*: v) = GOrderingOf u
  gordering (lt0 :*: lt1) (eq0 :*: eq1) (gt0 :*: gt1) o =
    gordering lt0 eq0 gt0 o :*: gordering lt1 eq1 gt1 o
  gcompare (x0 :*: x1) (y0 :*: y1) = gcompare x0 y0 <> gcompare x1 y1

instance GOrd v => GOrd (M1 i c v) where
  type GOrderingOf (M1 i c v) = GOrderingOf v
  gordering (M1 ltCase) (M1 eqCase) (M1 gtCase) o =
    M1 (gordering ltCase eqCase gtCase o)
  gcompare (M1 x) (M1 y) = gcompare x y

instance Ord x => GOrd (Rec0 x) where
  type GOrderingOf (Rec0 x) = OrderingOf x
  gordering (K1 ltCase) (K1 eqCase) (K1 gtCase) o =
    K1 (ordering ltCase eqCase gtCase o)
  gcompare (K1 x) (K1 y) = compare x y
