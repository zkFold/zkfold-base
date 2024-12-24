{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Data.Logical
  ( Boolean (..)
  , all, any, and, or
  , Conditional (..)
  , ifThenElse
  , Eq (..)
  , elem
  , GConditional (..)
  , GEq (..)
  ) where

import           Control.Category
import qualified Data.Bool                        as H
import           Data.Foldable                    hiding (all, and, any, elem, or)
import           Data.Functor.Identity
import qualified Data.Functor.Rep                 as R
import           Data.Kind
import qualified GHC.Generics                     as G
import           Prelude                          (type (~))
import qualified Prelude                          as H

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector

class Boolean b where

  true, false :: b

  not :: b -> b

  (&&), (||), xor :: b -> b -> b

instance Boolean H.Bool where
  true = H.True
  false = H.False
  not = H.not
  (&&) = (H.&&)
  (||) = (H.||)
  xor = (H./=)

all :: (Boolean b, Foldable t) => (x -> b) -> t x -> b
all f = foldr ((&&) . f) true

any :: (Boolean b, Foldable t) => (x -> b) -> t x -> b
any f = foldr ((||) . f) false

and :: (Boolean b, Foldable t) => t b -> b
and = all id

or :: (Boolean b, Foldable t) => t b -> b
or = any id

class Boolean (BooleanOf a) => Conditional a where

  type BooleanOf a :: Type
  type BooleanOf a = GBooleanOf (G.Rep a)

  bool :: a -> a -> BooleanOf a -> a
  default bool ::
    ( G.Generic a
    , GConditional (G.Rep a)
    , BooleanOf a ~ GBooleanOf (G.Rep a)
    ) => a -> a -> BooleanOf a -> a
  bool f t b = G.to (gbool (G.from f) (G.from t) b)

instance Conditional y => Conditional (x -> y) where
  type BooleanOf (x -> y) = BooleanOf y
  bool f t b x = bool (f x) (t x) b

instance
  ( Conditional x0
  , Conditional x1
  , BooleanOf x0 ~ BooleanOf x1
  ) => Conditional (x0,x1)

instance
  ( Conditional x0
  , Conditional x1
  , Conditional x2
  , BooleanOf x0 ~ BooleanOf x1
  , BooleanOf x1 ~ BooleanOf x2
  ) => Conditional (x0,x1,x2)

instance
  ( Conditional x0
  , Conditional x1
  , Conditional x2
  , Conditional x3
  , BooleanOf x0 ~ BooleanOf x1
  , BooleanOf x1 ~ BooleanOf x2
  , BooleanOf x2 ~ BooleanOf x3
  ) => Conditional (x0,x1,x2,x3)

instance (R.Representable v, Conditional x)
  => Conditional (G.Generically1 v x) where
    type BooleanOf (G.Generically1 v x) = BooleanOf x
    bool (G.Generically1 vf) (G.Generically1 vt) b =
      G.Generically1 (R.mzipWithRep (\f t -> bool f t b) vf vt)

deriving via G.Generically1 (Vector n) x
  instance (KnownNat n, Conditional x) => Conditional (Vector n x)

instance Conditional (Identity x) where
  type BooleanOf (Identity x) = H.Bool
  bool = H.bool

ifThenElse :: Conditional a => BooleanOf a -> a -> a -> a
ifThenElse b t f = bool f t b

class Conditional a => Eq a where

  (==) :: a -> a -> BooleanOf a
  default (==) ::
    ( G.Generic a
    , GEq (G.Rep a)
    , BooleanOf a ~ GBooleanOf (G.Rep a)
    ) => a -> a -> BooleanOf a
  x == y = geq (G.from x) (G.from y)

  (/=) :: a -> a -> BooleanOf a
  default (/=) ::
    ( G.Generic a
    , GEq (G.Rep a)
    , BooleanOf a ~ GBooleanOf (G.Rep a)
    ) => a -> a -> BooleanOf a
  x /= y = gneq (G.from x) (G.from y)

instance
  ( Eq x0, Eq x1
  , BooleanOf x0 ~ BooleanOf x1
  ) => Eq (x0,x1)

instance
  ( Eq x0
  , Eq x1
  , Eq x2
  , BooleanOf x0 ~ BooleanOf x1
  , BooleanOf x1 ~ BooleanOf x2
  ) => Eq (x0,x1,x2)

instance
  ( Eq x0
  , Eq x1
  , Eq x2
  , Eq x3
  , BooleanOf x0 ~ BooleanOf x1
  , BooleanOf x1 ~ BooleanOf x2
  , BooleanOf x2 ~ BooleanOf x3
  ) => Eq (x0,x1,x2,x3)

instance (Foldable v, R.Representable v, Eq x)
  => Eq (G.Generically1 v x) where
    G.Generically1 vx == G.Generically1 vy =
      and (R.mzipWithRep (==) vx vy)
    G.Generically1 vx /= G.Generically1 vy =
      or (R.mzipWithRep (==) vx vy)

deriving via G.Generically1 (Vector n) x
  instance (KnownNat n, Eq x) => Eq (Vector n x)

instance H.Eq x => Eq (Identity x) where
  (==) = (H.==)
  (/=) = (H./=)

elem :: (Eq a, Foldable t) => a -> t a -> BooleanOf a
elem x = any (== x)

class Boolean (GBooleanOf f) => GConditional f where
  type GBooleanOf f :: Type
  gbool :: f a -> f a -> GBooleanOf f -> f a

instance
  ( GConditional u
  , GConditional v
  , Boolean (GBooleanOf u)
  , GBooleanOf u ~ GBooleanOf v
  ) => GConditional (u G.:*: v) where
  type GBooleanOf (u G.:*: v) = GBooleanOf u
  gbool (f0 G.:*: f1) (t0 G.:*: t1) b = gbool f0 t0 b G.:*: gbool f1 t1 b

instance (R.Representable v, GConditional u)
  => GConditional (v G.:.: u) where
    type GBooleanOf (v G.:.: u) = GBooleanOf u
    gbool (G.Comp1 vf) (G.Comp1 vt) b =
      G.Comp1 (R.mzipWithRep (\f t -> gbool f t b) vf vt)

instance GConditional v => GConditional (G.M1 i c v) where
  type GBooleanOf (G.M1 i c v) = GBooleanOf v
  gbool (G.M1 f) (G.M1 t) b = G.M1 (gbool f t b)

instance Conditional x => GConditional (G.K1 i x) where
  type GBooleanOf (G.K1 i x) = BooleanOf x
  gbool (G.K1 f) (G.K1 t) b = G.K1 (bool f t b)

class GConditional f => GEq f where
  geq :: f a -> f a -> GBooleanOf f
  gneq :: f a -> f a -> GBooleanOf f

instance
  ( GEq u, GEq v
  , GBooleanOf u ~ GBooleanOf v
  ) => GEq (u G.:*: v) where
  geq (x0 G.:*: x1) (y0 G.:*: y1) = geq x0 y0 && geq x1 y1
  gneq (x0 G.:*: x1) (y0 G.:*: y1) = gneq x0 y0 || gneq x1 y1

instance (Foldable v, R.Representable v, GEq u) => GEq (v G.:.: u) where
  geq (G.Comp1 vx) (G.Comp1 vy) = and (R.mzipWithRep geq vx vy)
  gneq (G.Comp1 vx) (G.Comp1 vy) = or (R.mzipWithRep gneq vx vy)

instance GEq v => GEq (G.M1 i c v) where
  geq (G.M1 x) (G.M1 y) = geq x y
  gneq (G.M1 x) (G.M1 y) = gneq x y

instance Eq x => GEq (G.K1 i x) where
  geq (G.K1 x) (G.K1 y) = x == y
  gneq (G.K1 x) (G.K1 y) = x /= y
