{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Data.Conditional
  ( Conditional (..)
  , GConditional (..)
  ) where

import qualified Data.Bool                        as H
import           Data.Functor.Identity
import qualified Data.Functor.Rep                 as R
import           Data.Kind
import qualified GHC.Generics                     as G
import           Prelude                          (type (~))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Boolean
import           ZkFold.Base.Data.Vector

class Boolean (BooleanOf a) => Conditional a where

  type BooleanOf a :: Type
  type BooleanOf a = GBooleanOf (G.Rep a)

  ifThenElse :: BooleanOf a -> a -> a -> a
  default ifThenElse ::
    ( G.Generic a
    , GConditional (G.Rep a)
    , BooleanOf a ~ GBooleanOf (G.Rep a)
    ) => BooleanOf a -> a -> a -> a
  ifThenElse b t f = G.to (gifThenElse b (G.from t) (G.from f))

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
    ifThenElse b (G.Generically1 vt) (G.Generically1 vf) =
      G.Generically1 (R.mzipWithRep (ifThenElse b) vt vf)

deriving via G.Generically1 (Vector n) x
  instance (KnownNat n, Conditional x) => Conditional (Vector n x)

deriving via G.Generically1 ((->) x) y
  instance Conditional y => Conditional (x -> y)

instance Conditional (Identity x) where
  type BooleanOf (Identity x) = H.Bool
  ifThenElse b t f = if b then t else f

class Boolean (GBooleanOf f) => GConditional f where
  type GBooleanOf f :: Type
  gifThenElse :: GBooleanOf f -> f a -> f a -> f a

instance
  ( GConditional u
  , GConditional v
  , Boolean (GBooleanOf u)
  , GBooleanOf u ~ GBooleanOf v
  ) => GConditional (u G.:*: v) where
  type GBooleanOf (u G.:*: v) = GBooleanOf u
  gifThenElse b (t0 G.:*: t1) (f0 G.:*: f1) =
    gifThenElse b t0 f0 G.:*: gifThenElse b t1 f1

instance (R.Representable v, GConditional u)
  => GConditional (v G.:.: u) where
    type GBooleanOf (v G.:.: u) = GBooleanOf u
    gifThenElse b (G.Comp1 vt) (G.Comp1 vf) =
      G.Comp1 (R.mzipWithRep (gifThenElse b) vt vf)

instance GConditional v => GConditional (G.M1 i c v) where
  type GBooleanOf (G.M1 i c v) = GBooleanOf v
  gifThenElse b (G.M1 t) (G.M1 f) = G.M1 (gifThenElse b t f)

instance Conditional x => GConditional (G.K1 i x) where
  type GBooleanOf (G.K1 i x) = BooleanOf x
  gifThenElse b (G.K1 t) (G.K1 f) = G.K1 (ifThenElse b t f)
