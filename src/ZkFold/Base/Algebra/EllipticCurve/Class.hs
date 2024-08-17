{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Algebra.EllipticCurve.Class where

import           Data.Functor                    ((<&>))
import           Data.Kind                       (Type)
import           Numeric.Natural                 (Natural)
import           Prelude                         hiding (Num (..), sum, (/), (^))
import           Test.QuickCheck                 hiding (scale)

import           ZkFold.Base.Algebra.Basic.Class


data Point curve = Point { _x :: BaseField curve, _y :: BaseField curve } | Inf

class EllipticCurve curve where

    type BaseField curve :: Type
    type ScalarField curve :: Type

    inf :: Point curve

    gen :: Point curve

    add :: Point curve -> Point curve -> Point curve

    mul :: ScalarField curve -> Point curve -> Point curve

instance (EllipticCurve curve, Show (BaseField curve)) => Show (Point curve) where
    show Inf         = "Inf"
    show (Point x y) = "(" ++ show x ++ ", " ++ show y ++ ")"

instance (EllipticCurve curve, Eq (BaseField curve)) => Eq (Point curve) where
    Inf         == Inf         = True
    Inf         == _           = False
    _           == Inf         = False
    Point x1 y1 == Point x2 y2 = x1 == x2 && y1 == y2

instance EllipticCurve curve => AdditiveSemigroup (Point curve) where
    (+) = add

instance EllipticCurve curve => Scale Natural (Point curve) where
    scale = natScale

instance EllipticCurve curve => AdditiveMonoid (Point curve) where
    zero = Inf

instance (EllipticCurve curve, AdditiveGroup (BaseField curve)) => Scale Integer (Point curve) where
    scale = intScale

instance (EllipticCurve curve, AdditiveGroup (BaseField curve)) => AdditiveGroup (Point curve) where
    negate = pointNegate

instance (EllipticCurve curve, Arbitrary (ScalarField curve)) => Arbitrary (Point curve) where
    arbitrary = arbitrary <&> (`mul` gen)

class (EllipticCurve curve1, EllipticCurve curve2, ScalarField curve1 ~ ScalarField curve2,
        Eq (TargetGroup curve1 curve2), MultiplicativeGroup (TargetGroup curve1 curve2),
        Exponent (TargetGroup curve1 curve2) (ScalarField curve1)) => Pairing curve1 curve2 where
    type TargetGroup curve1 curve2 :: Type
    pairing :: Point curve1 -> Point curve2 -> TargetGroup curve1 curve2

pointAdd
    :: Field (BaseField curve)
    => Eq (BaseField curve)
    => Point curve
    -> Point curve
    -> Point curve
pointAdd p   Inf     = p
pointAdd Inf q       = q
pointAdd (Point x1 y1) (Point x2 y2)
  | x1 == x2  = Inf
  | otherwise = Point x3 y3
  where
    slope  = (y1 - y2) // (x1 - x2)
    x3 = slope * slope - x1 - x2
    y3 = slope * (x1 - x3) - y1

pointDouble
    :: Field (BaseField curve)
    => Point curve -> Point curve
pointDouble Inf = Inf
pointDouble (Point x y) = Point x' y'
  where
    slope = (x * x + x * x + x * x) // (y + y)
    x' = slope * slope - x - x
    y' = slope * (x - x') - y

addPoints
    :: EllipticCurve curve
    => Field (BaseField curve)
    => Eq (BaseField curve)
    => Point curve
    -> Point curve
    -> Point curve
addPoints p1 p2
    | p1 == p2  = pointDouble p1
    | otherwise = pointAdd p1 p2

pointNegate
    :: AdditiveGroup (BaseField curve)
    => Point curve -> Point curve
pointNegate Inf         = Inf
pointNegate (Point x y) = Point x (negate y)

pointMul
    :: forall curve
    .  EllipticCurve curve
    => BinaryExpansion (ScalarField curve)
    => Bits (ScalarField curve) ~ [ScalarField curve]
    => Eq (ScalarField curve)
    => ScalarField curve
    -> Point curve
    -> Point curve
pointMul = natScale . fromBinary . castBits . binaryExpansion

-- An elliptic curve in standard form, y^2 = x^3 + a * x + b
class EllipticCurve curve => StandardEllipticCurve curve where
    aParameter :: BaseField curve
    bParameter :: BaseField curve

data PointCompressed curve = PointCompressed (BaseField curve) Bool | InfCompressed

instance Show (BaseField curve) => Show (PointCompressed curve) where
    show InfCompressed            = "InfCompressed"
    show (PointCompressed x bigY) = "(" ++ show x ++ ", " ++ show bigY ++ ")"

deriving instance Eq (BaseField curve) => Eq (PointCompressed curve)

instance (Arbitrary (Point curve), AdditiveGroup (BaseField curve), Ord (BaseField curve)
        ) => Arbitrary (PointCompressed curve) where
    arbitrary = compress <$> arbitrary

compress
  :: ( AdditiveGroup (BaseField curve)
     , Ord (BaseField curve)
     )
  => Point curve -> PointCompressed curve
compress = \case
  Inf -> InfCompressed
  Point x y -> PointCompressed x (y > negate y)

decompress
  :: forall curve .
     ( StandardEllipticCurve curve
     , FiniteField (BaseField curve)
     , Ord (BaseField curve)
     )
  => PointCompressed curve -> Point curve
decompress = \case
  InfCompressed -> Inf
  PointCompressed x bigY ->
    let a = aParameter @curve
        b = bParameter @curve
        p = order @(BaseField curve)
        sqrt_ z = z ^ ((p + 1) `Prelude.div` 2)
        y' = sqrt_ (x * x * x + a * x + b)
        y = (if bigY then maximum else minimum) [y', negate y']
    in
        Point x y
