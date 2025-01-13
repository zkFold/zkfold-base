{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module ZkFold.Base.Algebra.EllipticCurve.Class
  ( -- * curve classes
    EllipticCurve (..)
  , CyclicGroup (..)
  , WeierstrassCurve (..)
  , TwistedEdwardsCurve (..)
  , CompressiblePoint (..)
  , Pairing (..)
    -- * point classes
  , Planar (..)
  , HasPointInf (..)
    -- * point types
  , Weierstrass (..)
  , TwistedEdwards (..)
  , Point (..)
  , CompressedPoint (..)
  , AffinePoint (..)
  ) where

import           Data.Kind                        (Type)
import           Data.String                      (fromString)
import           GHC.Generics
import           GHC.TypeLits                     (Symbol)
import           Prelude                          (Integer, type (~))
import qualified Prelude

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.Input

{- | Elliptic curves are plane algebraic curves that form `AdditiveGroup`s.
Elliptic curves always have genus @1@ and are birationally equivalent
to a projective curve of degree @3@. As such, elliptic curves are
the simplest curves after conic sections, curves of degree @2@,
and lines, curves of degree @1@. Bézout's theorem implies
that a line in general position will intersect with an
elliptic curve at 3 points counting multiplicity;
@point0@, @point1@ and @point2@.
The geometric group law of the elliptic curve is:

> point0 + point1 + point2 = zero
-}
class
  ( Field (BaseFieldOf point)
  , Eq bool (BaseFieldOf point)
  , Planar (BaseFieldOf point) point
  , AdditiveGroup point
  ) => EllipticCurve bool point where
    type CurveOf point :: Symbol
    type BaseFieldOf point :: Type
    -- | `isOnCurve` validates an equation for a plane algebraic curve
    -- which has degree 3 up to some birational equivalence.
    isOnCurve :: point -> bool

{- | Both the ECDSA and ECDH algorithms make use of
the elliptic curve discrete logarithm problem, ECDLP.
There may be a discrete "exponential" function
from a `PrimeField` of scalars
into the `AdditiveGroup` of points on an elliptic curve.
It's given naturally by scaling a point of prime order,
if there is one on the curve.

prop> scale order pointGen = zero

>>> let discreteExp scalar = scale scalar pointGen

Then the inverse of `discreteExp` is hard to compute.
-}
class
  ( AdditiveGroup g
  , FiniteField (ScalarFieldOf g)
  , Scale (ScalarFieldOf g) g
  ) => CyclicGroup g where
    type ScalarFieldOf g :: Type
    -- | generator of a cyclic subgroup
    --
    -- prop> scale (order @(ScalarFieldOf g)) pointGen = zero
    pointGen :: g

{- | The standard form of an elliptic curve is the Weierstrass equation:

> y^2 = x^3 + a*x + b

* Weierstrass curves have x-axis symmetry.
* The characteristic of the field must not be @2@ or @3@.
* The curve must have nonzero discriminant @Δ = -16 * (4*a^3 + 27*b^3)@.
* When @a = 0@ some computations can be simplified so all the public
  Weierstrass curves have @a = zero@ and nonzero @b@ and we do too.
-}
class Field field => WeierstrassCurve (curve :: Symbol) field where
  weierstrassB :: field

{- | A twisted Edwards curve is defined by the equation:

> a*x^2 + y^2 = 1 + d*x^2*y^2

* Twisted Edwards curves have y-axis symmetry.
* The characteristic of the field must not be @2@.
* @a@ and @d@ must be nonzero.
-}
class Field field => TwistedEdwardsCurve (curve :: Symbol) field where
  twistedEdwardsA :: field
  twistedEdwardsD :: field

class CompressiblePoint bool point where
  type CompressedPointOf point :: Type
  pointCompressed :: BaseFieldOf point -> bool -> pt
  compressPoint :: point -> pt
  decompressPoint :: pt -> point

class
  ( Field field
  , AdditiveGroup g1, Scale field g1
  , AdditiveGroup g2, Scale field g2
  , MultiplicativeGroup gt, Exponent gt field
  ) => Pairing field g1 g2 gt | g1 g2 -> gt where
    pairing :: g1 -> g2 -> gt

{- | A class for smart constructor method
`pointXY` for constructing points from an @x@ and @y@ coordinate. -}
class Planar field point | point -> field where
  pointXY :: field -> field -> point

{- | A class for smart constructor method
`pointInf` for constructing the point at infinity. -}
class HasPointInf point where pointInf :: point

{- | `Weierstrass` tags a `ProjectivePlanar` @point@, over a `Field` @field@,
with a phantom `WeierstrassCurve` @curve@. -}
newtype Weierstrass curve point = Weierstrass {pointWeierstrass :: point}
instance
  ( WeierstrassCurve curve field
  , Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Field field
  ) => EllipticCurve bool (Weierstrass curve (Point bool field)) where
    type CurveOf (Weierstrass curve (Point bool field)) = curve
    type BaseFieldOf (Weierstrass curve (Point bool field)) = field
    isOnCurve (Weierstrass (Point x y isInf)) =
      if isInf then x == zero else
      let b = weierstrassB @curve in y*y == x*x*x + b
deriving newtype instance
  ( SymbolicOutput bool
  , SymbolicOutput field
  , Context field ~ Context bool
  ) => SymbolicData (Weierstrass curve (Point bool field))
instance
  ( SymbolicInput field
  , Context field ~ ctx
  , Symbolic ctx
  , WeierstrassCurve curve field
  , Eq (Bool ctx) field
  , Conditional (Bool ctx) field
  ) => SymbolicInput (Weierstrass curve (Point (Bool ctx) field)) where
    isValid = isOnCurve
deriving newtype instance Conditional bool point
  => Conditional bool (Weierstrass curve point)
deriving newtype instance Eq bool point
  => Eq bool (Weierstrass curve point)
deriving newtype instance HasPointInf point
  => HasPointInf (Weierstrass curve point)
deriving newtype instance Planar field point
  => Planar field (Weierstrass curve point)
instance
  ( WeierstrassCurve curve field
  , Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Field field
  ) => AdditiveSemigroup (Weierstrass curve (Point bool field)) where
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
  ) => AdditiveMonoid (Weierstrass curve (Point bool field)) where
    zero = pointInf
instance
  ( WeierstrassCurve curve field
  , Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Field field
  ) => AdditiveGroup (Weierstrass curve (Point bool field)) where
    negate pt@(Weierstrass (Point x y isInf)) =
      if isInf then pt else pointXY x (negate y)
instance
  ( WeierstrassCurve curve field
  , Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Field field
  ) => Scale Natural (Weierstrass curve (Point bool field)) where
  scale = natScale
instance
  ( WeierstrassCurve curve field
  , Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Field field
  ) => Scale Integer (Weierstrass curve (Point bool field)) where
  scale = intScale

{- | `TwistedEdwards` tags a `Planar` @point@, over a `Field` @field@,
with a phantom `TwistedEdwardsCurve` @curve@. -}
newtype TwistedEdwards curve point = TwistedEdwards {pointTwistedEdwards :: point}
instance
  ( TwistedEdwardsCurve curve field
  , Field field
  , Eq bool field
  ) => EllipticCurve bool (TwistedEdwards curve (AffinePoint field)) where
    type CurveOf (TwistedEdwards curve (AffinePoint field)) = curve
    type BaseFieldOf (TwistedEdwards curve (AffinePoint field)) = field
    isOnCurve (TwistedEdwards (AffinePoint x y)) =
      let a = twistedEdwardsA @curve
          d = twistedEdwardsD @curve
      in a*x*x + y*y == one + d*x*x*y*y
deriving newtype instance SymbolicOutput field
  => SymbolicData (TwistedEdwards curve (AffinePoint field))
instance
  ( SymbolicInput field
  , Context field ~ ctx
  , Symbolic ctx
  , TwistedEdwardsCurve curve field
  , Eq (Bool ctx) field
  , Conditional (Bool ctx) field
  ) => SymbolicInput (TwistedEdwards curve (AffinePoint field)) where
    isValid = isOnCurve
deriving newtype instance Conditional bool point
  => Conditional bool (TwistedEdwards curve point)
deriving newtype instance Eq bool point
  => Eq bool (TwistedEdwards curve point)
deriving newtype instance HasPointInf point
  => HasPointInf (TwistedEdwards curve point)
deriving newtype instance Planar field point
  => Planar field (TwistedEdwards curve point)
instance
  ( TwistedEdwardsCurve curve field
  , Field field
  ) => AdditiveSemigroup (TwistedEdwards curve (AffinePoint field)) where
    TwistedEdwards (AffinePoint x0 y0) + TwistedEdwards (AffinePoint x1 y1) =
      let a = twistedEdwardsA @curve
          d = twistedEdwardsD @curve
          x2 = (x0 * y1 + y0 * x1) // (one + d * x0 * x1 * y0 * y1)
          y2 = (y0 * y1 - a * x0 * x1) // (one - d * x0 * x1 * y0 * y1)
      in pointXY x2 y2
instance
  ( TwistedEdwardsCurve curve field
  , Field field
  ) => AdditiveMonoid (TwistedEdwards curve (AffinePoint field)) where
    zero = pointXY zero one
instance
  ( TwistedEdwardsCurve curve field
  , Field field
  ) => AdditiveGroup (TwistedEdwards curve (AffinePoint field)) where
    negate (TwistedEdwards (AffinePoint x y)) = pointXY (negate x) y
instance
  ( TwistedEdwardsCurve curve field
  , Field field
  ) => Scale Natural (TwistedEdwards curve (AffinePoint field)) where
  scale = natScale
instance
  ( TwistedEdwardsCurve curve field
  , Field field
  ) => Scale Integer (TwistedEdwards curve (AffinePoint field)) where
  scale = intScale

{- | A type of points in the projective plane. -}
data Point bool field = Point
  { _x    :: field
  , _y    :: field
  , _zBit :: bool
  } deriving Generic
instance
  ( SymbolicOutput bool
  , SymbolicOutput field
  , Context field ~ Context bool
  ) => SymbolicData (Point bool field)
instance BoolType bool => Planar field (Point bool field) where
  pointXY x y = Point x y false
instance (BoolType bool, Semiring field) => HasPointInf (Point bool field) where
  pointInf = Point zero one true
instance Prelude.Show field => Prelude.Show (Point Prelude.Bool field) where
  show (Point x y isInf) =
    if isInf then "pointInf" else Prelude.mconcat
      ["(", Prelude.show x, ", ", Prelude.show y, ")"]
instance
  ( Conditional bool bool
  , Conditional bool field
  ) => Conditional bool (Point bool field)
instance
  ( Conditional bool bool
  , Eq bool bool
  , Eq bool field
  , Field field
  ) => Eq bool (Point bool field) where
    Point x0 y0 isInf0 == Point x1 y1 isInf1 =
      if not isInf0 && not isInf1
      then x0 == x1 && y0 == y1
      else isInf0 && isInf1 && x1*y0 == x0*y1 -- same slope y0//x0 = y1//x1
    pt0 /= pt1 = not (pt0 == pt1)

data CompressedPoint bool field = CompressedPoint
  { _x    :: field
  , _yBit :: bool
  , _zBit :: bool
  } deriving Generic
instance
  ( SymbolicOutput bool
  , SymbolicOutput field
  , Context field ~ Context bool
  ) => SymbolicData (CompressedPoint bool field)
instance (BoolType bool, AdditiveMonoid field)
  => HasPointInf (CompressedPoint bool field) where
    pointInf = CompressedPoint zero true true

data AffinePoint field = AffinePoint
  { _x :: field
  , _y :: field
  } deriving Generic
instance SymbolicOutput field => SymbolicData (AffinePoint field)
instance Planar field (AffinePoint field) where pointXY = AffinePoint
instance Conditional bool field => Conditional bool (AffinePoint field)
instance
  ( BoolType bool
  , Eq bool field
  , Field field
  ) => Eq bool (AffinePoint field)
