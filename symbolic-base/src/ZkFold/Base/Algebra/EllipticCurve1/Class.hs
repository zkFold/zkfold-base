{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module ZkFold.Base.Algebra.EllipticCurve1.Class where

import           Data.Functor                     ((<&>))
import           Data.Kind                        (Type)
import           Data.String                      (fromString)
import           GHC.Generics                     (Generic)
import           GHC.TypeLits                     (Symbol)
import           Prelude                          (Integer, Show (..), fromInteger, type (~), (++), (.), (<$>))
import qualified Prelude                          as P
import           Test.QuickCheck                  hiding (scale)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Symbolic.Class            (Symbolic)
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.Ord

data Point (curve :: Type) = Point
  { _x     :: BaseField curve
  , _y     :: BaseField curve
  , _isInf :: BooleanOf curve
  } deriving (Generic)

instance
  ( EllipticCurve curve
  , bool ~ BooleanOf curve
  ) => Conditional bool (Point curve)

instance
  ( EllipticCurve curve
  , bool ~ BooleanOf curve
  ) => Eq bool (Point curve)

instance
  ( EllipticCurve curve
  , BooleanOf curve ~ P.Bool
  ) => P.Eq (Point curve) where
  (==) = (==)
  (/=) = (/=)

instance
  ( Symbolic ctx
  , SymbolicOutput bool
  , SymbolicOutput field
  , bool ~ BooleanOf curve
  , field ~ BaseField curve
  , Context bool ~ ctx
  , Context field ~ ctx
  ) => SymbolicData (Point curve)

class Planar field plane where
  pointXY :: field -> field -> plane

instance
  ( field ~ BaseField curve
  , bool ~ BooleanOf curve
  , BoolType bool
  ) => Planar field (Point curve) where
  pointXY x y = Point x y false

class ProjectivePlanar plane where
  pointInf :: plane

instance
  ( field ~ BaseField curve
  , BoolType (BooleanOf curve)
  , AdditiveMonoid field
  ) => ProjectivePlanar (Point curve) where
  pointInf = Point zero zero true

instance
  ( field ~ BaseField curve
  , BoolType (BooleanOf curve)
  , AdditiveMonoid field
  ) => ProjectivePlanar (CompressedPoint curve) where
  pointInf = CompressedPoint zero false true

class
    ( BoolType (BooleanOf curve)
    , AdditiveMonoid (BaseField curve)
    , Conditional (BooleanOf curve) (BaseField curve)
    , Conditional (BooleanOf curve) (BooleanOf curve)
    , Eq (BooleanOf curve) (BaseField curve)
    , Eq (BooleanOf curve) (BooleanOf curve)
    ) => EllipticCurve curve where

    type BaseField curve :: Type
    type ScalarField curve :: Type
    type BooleanOf curve :: Type
    type BooleanOf curve = P.Bool

    pointGen :: Point curve

    add :: Point curve -> Point curve -> Point curve

    mul :: ScalarField curve -> Point curve -> Point curve

instance
  ( EllipticCurve curve
  , Show (BaseField curve)
  , Conditional (BooleanOf curve) P.String
  ) => Show (Point curve) where
    show (Point x y isInf) = if isInf then "Inf" else "(" ++ show x ++ ", " ++ show y ++ ")"

instance EllipticCurve curve => AdditiveSemigroup (Point curve) where
    (+) = add

instance {-# OVERLAPPABLE #-}
    ( EllipticCurve curve
    , BooleanOf curve ~ P.Bool
    , P.Eq s
    , BinaryExpansion s
    , Bits s ~ [s]
    ) => Scale s (Point curve) where
    scale = pointMul

instance EllipticCurve curve => Scale Natural (Point curve) where
    scale = natScale

instance EllipticCurve curve => AdditiveMonoid (Point curve) where
    zero = pointInf

instance (EllipticCurve curve, AdditiveGroup (BaseField curve)) => Scale Integer (Point curve) where
    scale = intScale

instance (EllipticCurve curve, AdditiveGroup (BaseField curve)) => AdditiveGroup (Point curve) where
    negate = pointNegate

instance (EllipticCurve curve, Arbitrary (ScalarField curve)) => Arbitrary (Point curve) where
    arbitrary = arbitrary <&> (`mul` pointGen)

class (EllipticCurve curve1, EllipticCurve curve2, ScalarField curve1 ~ ScalarField curve2,
        P.Eq (TargetGroup curve1 curve2), MultiplicativeGroup (TargetGroup curve1 curve2),
        Exponent (TargetGroup curve1 curve2) (ScalarField curve1)) => Pairing curve1 curve2 where
    type TargetGroup curve1 curve2 :: Type
    pairing :: Point curve1 -> Point curve2 -> TargetGroup curve1 curve2

pointAdd
    :: EllipticCurve curve
    => Field (BaseField curve)
    => Point curve
    -> Point curve
    -> Point curve
pointAdd p@(Point x1 y1 isInf1) q@(Point x2 y2 isInf2) =
  if isInf2 then p
  else if isInf1 then q
  else if x1 == x2 then pointInf
  else pointXY x3 y3
  where
    slope  = (y1 - y2) // (x1 - x2)
    x3 = slope * slope - x1 - x2
    y3 = slope * (x1 - x3) - y1

pointDouble
    :: EllipticCurve curve
    => Field (BaseField curve)
    => Point curve -> Point curve
pointDouble (Point x y isInf) = if isInf then pointInf else pointXY x' y'
  where
    slope = (x * x + x * x + x * x) // (y + y)
    x' = slope * slope - x - x
    y' = slope * (x - x') - y

addPoints
    :: EllipticCurve curve
    => Field (BaseField curve)
    => Point curve
    -> Point curve
    -> Point curve
addPoints p1 p2 = if p1 == p2 then pointDouble p1 else pointAdd p1 p2

pointNegate
    :: EllipticCurve curve
    => AdditiveGroup (BaseField curve)
    => Point curve -> Point curve
pointNegate (Point x y isInf) = if isInf then pointInf else pointXY x (negate y)

pointMul
    :: forall curve s
    .  EllipticCurve curve
    => BinaryExpansion (s)
    => Bits s ~ [s]
    => P.Eq s
    => s
    -> Point curve
    -> Point curve
pointMul = natScale . fromBinary . castBits . binaryExpansion

-- An elliptic curve in standard form, y^2 = x^3 + a * x + b
class EllipticCurve curve => WeierstrassCurve curve where
  weierstrassA :: BaseField curve
  weierstrassB :: BaseField curve

data CompressedPoint curve = CompressedPoint
  { _x     :: BaseField curve
  , _bigY  :: BooleanOf curve
  , _isInf :: BooleanOf curve
  } deriving Generic

pointCompressed :: BoolType (BooleanOf curve) => BaseField curve -> BooleanOf curve -> CompressedPoint curve
pointCompressed x bigY = CompressedPoint x bigY false

instance
  ( EllipticCurve curve
  , bool ~ BooleanOf curve
  ) => Conditional bool (CompressedPoint curve)

instance
  ( EllipticCurve curve
  , bool ~ BooleanOf curve
  ) => Eq bool (CompressedPoint curve)

instance
  ( EllipticCurve curve
  , BooleanOf curve ~ P.Bool
  ) => P.Eq (CompressedPoint curve) where
  (==) = (==)
  (/=) = (/=)

instance
  ( Show (BaseField curve)
  , Conditional (BooleanOf curve) P.String
  , Show (BooleanOf curve)
  ) => Show (CompressedPoint curve) where
    show (CompressedPoint x bigY isInf) =
      if isInf then "InfCompressed" else "(" ++ show x ++ ", " ++ show bigY ++ ")"

instance
  ( EllipticCurve curve
  , AdditiveGroup (BaseField curve)
  , Ord (BooleanOf curve) (BaseField curve)
  , Arbitrary (ScalarField curve)
  ) => Arbitrary (CompressedPoint curve) where
    arbitrary = compress <$> arbitrary

compress
  :: ( AdditiveGroup (BaseField curve)
     , EllipticCurve curve
     , Ord (BooleanOf curve) (BaseField curve)
     )
  => Point curve -> CompressedPoint curve
compress = \case
  Point x y isInf -> if isInf then pointInf else CompressedPoint x (y > negate y) false

decompress
  :: forall curve .
     ( WeierstrassCurve curve
     , FiniteField (BaseField curve)
     , Ord (BooleanOf curve) (BaseField curve)
     )
  => CompressedPoint curve -> Point curve
decompress (CompressedPoint x bigY isInf) =
  if isInf then pointInf else
    let a = weierstrassA @curve
        b = weierstrassB @curve
        p = order @(BaseField curve)
        sqrt_ z = z ^ ((p + 1) `P.div` 2)
        y' = sqrt_ (x * x * x + a * x + b)
        y'' = negate y'
        y = if bigY then max @(BooleanOf curve) y' y'' else min @(BooleanOf curve) y' y''
    in
        pointXY x y
