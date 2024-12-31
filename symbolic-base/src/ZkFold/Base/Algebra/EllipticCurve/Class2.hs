{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module ZkFold.Base.Algebra.EllipticCurve.Class2
  ( -- * curve classes
    EllipticCurve (..)
  , SubgroupCurve (..)
  , WeierstrassCurve (..)
    -- * point classes
  , Planar (..)
  , HasPointInf (..)
  , ProjectivePlanar (..)
    -- * point types
  , Weierstrass (..)
  , Point (..)
  , CompressedPoint (..)
  , AffinePoint (..)
  , CompressedAffinePoint (..)
  , TwistedEdwardsPoint (..)
  , Slope (..)
  ) where

import GHC.Generics
import Prelude (Integer)

import ZkFold.Base.Algebra.Basic.Class
import ZkFold.Base.Algebra.Basic.Number
import ZkFold.Symbolic.Data.Bool
import ZkFold.Symbolic.Data.Conditional
import ZkFold.Symbolic.Data.Eq

{- | Elliptic curves are plane algebraic curves that form `AdditiveGroup`s.
Elliptic curves always have genus @1@ and are birationally equivalent
to a projective curve of degree @3@. As such, elliptic curves are
the least complicated curves after conic sections, curves of
degree @2@, and lines, curves of degree @1@. Bézout's theorem implies
that a line in general position will intersect with an
elliptic curve at 3 points counting multiplicity;
@point0@, @point1@ and @point2@.
The geometric group law of the elliptic curve is:

> point0 + point1 + point2 = zero
-}
class
  ( Field field
  , Eq bool field
  , Planar point
  , AdditiveGroup (point field)
  ) => EllipticCurve curve bool field point where
    -- | `isOnCurve` validates an equation for an plane algebraic curve
    -- which has degree 3 up to some birational equivalence.
    isOnCurve :: point field -> bool

{- | Both the ECDSA and ECDH algorithms make use of
the elliptic curve discrete logarithm problem, ECDLP.
There is a discrete "exponential" function
from a finite prime field @scalarField@
to the group of points on an elliptic curve,
given naturally by scaling a point of prime order,
if there is one, constructed by the method `pointGen`.
Then the inverse of the discrete exponential is hard to compute.
-}
class
  ( EllipticCurve curve bool baseField point
  , FiniteField scalarField
  , Scale scalarField (point baseField)
  ) => SubgroupCurve curve bool baseField scalarField point where
    -- | generator of a cyclic subgroup of the curve of prime order
    pointGen :: point baseField

{- | The standard form of an elliptic curve is the Weierstrass equation:

> y^2 = x^3 + a*x + b

When @a = 0@ some computations can be simplified so all the public standard
Weierstrass curves have @a = 0@ and we make that assumption too. -}
class Field field => WeierstrassCurve curve field where weierstrassB :: field

{- | A class for smart constructor method
`pointXY` for constructing points from an @x@ and @y@ coordinate. -}
class Planar point where pointXY :: field -> field -> point field

{- | A class for smart constructor method
`pointInf` for constructing the point at infinity. -}
class HasPointInf point where pointInf :: point

{- | A class with a destructor method
`casePoint` for handling finite and infinite points. -}
class
  ( BoolType bool
  , Planar point
  , HasPointInf (point field)
  , Conditional bool (point field)
  , Eq bool (point field)
  , FromConstant (AffinePoint field) (point field)
  , FromConstant (Slope field) (point field)
  ) => ProjectivePlanar bool field point where


    {- | `casePoint` expresses points as a disjoint union of

          * finite `Planar` `AffinePoint`s;
          * the projective line of `Slope`s at infinity.

          Embedding finite and infinite points with `fromConstant`,

          prop> fromConstant (pointXY x y) = pointXY x y
          prop> fromConstant pointInf = pointInf

          And up to `Eq`uality of points,

          prop> id = casePoint fromConstant fromConstant
    -}
    casePoint
      :: (Conditional bool r, Eq bool r)
      => (AffinePoint field -> r) -- ^ finite case
      -> (Slope field -> r) -- ^ infinite case
      -> point field -> r

{- | `Weierstrass` tags a `ProjectivePlanar` @point@, over a `Field` @field@,
with a phantom `WeierstrassCurve` @curve@. -}
newtype Weierstrass curve point field = Weierstrass {pointWeierstrass :: point field}
deriving newtype instance Conditional bool (point field)
  => Conditional bool (Weierstrass curve point field)
deriving newtype instance Eq bool (point field)
  => Eq bool (Weierstrass curve point field)
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

{- | A type of points in the projective plane.

For finite `AffinePoint`s,

prop> Point x y true = fromConstant (AffinePoint x y)

For the projective line of `Slope`s at infinity,

prop> Point x y false = fromConstant (Slope x y)
-}
data Point bool field = Point
  { _x :: field
  , _y :: field
  , _zBit :: bool
  } deriving Generic
instance BoolType bool => Planar (Point bool) where
  pointXY x y = Point x y false
instance BoolType bool
  => FromConstant (Slope field) (Point bool field) where
    fromConstant (Slope x y) = Point x y true
instance BoolType bool
  => FromConstant (AffinePoint field) (Point bool field) where
    fromConstant (AffinePoint x y) = Point x y false
instance
  ( BoolType bool
  , Semiring field
  ) => HasPointInf (Point bool field) where
  pointInf = Point zero one true
instance
  ( Conditional bool bool
  , Conditional bool field
  , Eq bool bool
  , Eq bool field
  , Field field
  ) => ProjectivePlanar bool field (Point bool) where
    casePoint fin infin (Point x y isInf) =
      if isInf then infin (Slope x y) else fin (pointXY x y) 
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

data CompressedPoint bool field = CompressedPoint
  { _x :: field
  , _yBit :: bool
  , _zBit :: bool
  } deriving Generic

data AffinePoint field = AffinePoint
  { _x :: field
  , _y :: field
  } deriving Generic
instance Planar AffinePoint where pointXY = AffinePoint

data CompressedAffinePoint bool field = CompressedAffinePoint
  { _xBit :: bool
  , _y :: field
  } deriving Generic

data HomogeneousPoint field = HomogeneousPoint
  { _x :: field
  , _y :: field
  , _z :: field
  } deriving Generic

data TwistedEdwardsPoint field = TwistedEdwardsPoint
  { _x :: field
  , _y :: field
  , _t :: field
  , _z :: field
  } deriving Generic

data Slope field = Slope
  { _x :: field
  , _y :: field
  } deriving Generic
