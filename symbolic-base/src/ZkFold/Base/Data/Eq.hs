{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeOperators        #-}

module ZkFold.Base.Data.Eq
  ( Eq (..)
  , elem
  , GEq (..)
  ) where

import           Data.Foldable                    hiding (all, and, any, elem, or)
import           Data.Functor.Identity
import qualified Data.Functor.Rep                 as R
import qualified GHC.Generics                     as G
import           Prelude                          (type (~))
import qualified Prelude                          as H

import           ZkFold.Base.Data.Boolean
import           ZkFold.Base.Data.Conditional
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector

class Conditional a => Eq a where

  (==) :: a -> a -> BooleanOf a
  default (==) ::
    ( G.Generic a
    , GEq (G.Rep a)
    , BooleanOf a ~ GBooleanOf (G.Rep a)
    ) => a -> a -> BooleanOf a
  x == y = geq (G.from x) (G.from y)

  (/=) :: a -> a -> BooleanOf a
  x /= y = not (x == y)

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
      or (R.mzipWithRep (/=) vx vy)

deriving via G.Generically1 (Vector n) x
  instance (KnownNat n, Eq x) => Eq (Vector n x)

instance H.Eq x => Eq (Identity x) where
  (==) = (H.==)
  (/=) = (H./=)

elem :: (Eq a, Foldable t) => a -> t a -> BooleanOf a
elem x = any (== x)

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
