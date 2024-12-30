{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module ZkFold.Base.Algebra.EllipticCurve.Class2
  ( EllipticCurve (..)
  , WeierstrassCurve (..)
  , Planar (..)
  , HasPointInf (..)
  , Point (..)
  , Weierstrass (..)
  ) where

import GHC.Generics
import Prelude (Integer)

import ZkFold.Base.Algebra.Basic.Class
import ZkFold.Base.Algebra.Basic.Number
import ZkFold.Symbolic.Data.Bool
import ZkFold.Symbolic.Data.Conditional
import ZkFold.Symbolic.Data.Eq

{- | Elliptic curves are algebraic curves that form Abelian groups.
Elliptic curves always have genus @1@ and are birationally equivalent
to a curve of degree @3@. As such, elliptic curves are geometrically
the least complicated curves after the conic sections, curves of
degree @2@ and lines, curves of degree @1@. By Bézout's theorem,
we know that a line in general position will intersect with an
elliptic curve at 3 points counting multiplicity;
@point0@, @point1@ and @point2@. The group laws of the elliptic curve are:

> point0 + point1 + point2 = zero
> pointInf = zero
-}
class
  ( Field field
  , Eq bool field
  , Planar point
  , AdditiveGroup (point field)
  ) => EllipticCurve curve bool field point where
    isOnCurve :: point field -> bool

{- | The standard form of an elliptic curve is the Weierstrass equation:

> y^2 = x^3 + A*x + B

When @A = 0@ some computations can be simplified so all the public standard
Weierstrass curves have @A = 0@ and we make that assumption too. -}
class WeierstrassCurve curve field where weierstrassB :: field

{- | A class for smart constructor method
`pointXY` for constructing points from an @x@ and @y@ coordinate.
-}
class Planar point where pointXY :: field -> field -> point field

{- | A class for smart constructor method
`pointInf` for constructing a point at infinity. -}
class HasPointInf point where pointInf :: point

{- | A type of points in the projective plane.

* When `_zBit` is `false`, then `_x` and `_y` are coordinates of a finite point.
* When `_zBit` is `true`, then `_y` `//` `_x` is
the coordinate of a point on the projective line at infinity.
-}
data Point bool field = Point
  { _x :: field
  , _y :: field
  , _zBit :: bool
  } deriving Generic
instance BoolType bool => Planar (Point bool) where
  pointXY x y = Point x y false
instance
  ( BoolType bool
  , Semiring field
  ) => HasPointInf (Point bool field) where
  pointInf = Point zero one true
instance
  ( BoolType bool
  , Conditional bool bool
  , Conditional bool field
  ) => Conditional bool (Point bool field)
instance
  ( BoolType bool
  , Conditional bool bool
  , Eq bool bool
  , Eq bool field
  , Field field
  ) => Eq bool (Point bool field) where
    Point x0 y0 isInf0 == Point x1 y1 isInf1 =
      if not isInf0 && not isInf1 then x0 == x1 && y0 == y1
      else if isInf0 && isInf1
      then x0 == zero && x1 == zero || x1*y0 == x0*y1 -- same slope y0//x0 = y1//x1
      else false
    pt0 /= pt1 = not (pt0 == pt1)

{- | `Weierstrass` newtype specifies a point on a particular `WeierstrassCurve`. -}
newtype Weierstrass curve point field = Weierstrass {pointWeierstrass :: point field}
deriving newtype instance Conditional bool (point field)
  => Conditional bool (Weierstrass curve point field)
deriving newtype instance HasPointInf (point field)
  => HasPointInf (Weierstrass curve point field)
deriving newtype instance Planar point
  => Planar (Weierstrass curve point)
instance
  ( WeierstrassCurve curve field
  , Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Field field
  ) => AdditiveSemigroup (Weierstrass curve (Point bool) field) where
    pt0@(Weierstrass (Point x0 y0 isInf0)) + pt1@(Weierstrass (Point x1 y1 isInf1)) =
      if isInf0 then pt1 else if isInf1 then pt0 -- additive identity
      else if x0 == x1 && y0 + y1 == zero :: bool then pointInf -- additive inverse
      else let slope = if x0 == x1 && y0 == y1 :: bool
                       then (x0 * x0 + x0 * x0 + x0 * x0) // (y0 + y0) -- tangent
                       else (y1 - y0) // (x1 - x0) -- secant
               x2 = slope * slope - x0 - x1
               y2 = slope * (x0 - x2) - y0
            in pointXY x2 y2
instance
  ( WeierstrassCurve curve field
  , Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Field field
  ) => AdditiveMonoid (Weierstrass curve (Point bool) field) where
    zero = pointInf
instance
  ( WeierstrassCurve curve field
  , Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Field field
  ) => AdditiveGroup (Weierstrass curve (Point bool) field) where
    negate pt@(Weierstrass (Point x y isInf)) =
      if isInf then pt else pointXY x (negate y)
instance
  ( WeierstrassCurve curve field
  , Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Field field
  ) => EllipticCurve curve bool field (Weierstrass curve (Point bool)) where
    isOnCurve (Weierstrass (Point x y isInf)) =
      if isInf then x == zero else
      let b = weierstrassB @curve in y*y == x*x*x + b
instance
  ( WeierstrassCurve curve field
  , Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Field field
  ) => Scale Natural (Weierstrass curve (Point bool) field) where
  scale = natScale
instance
  ( WeierstrassCurve curve field
  , Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Field field
  ) => Scale Integer (Weierstrass curve (Point bool) field) where
  scale = intScale
