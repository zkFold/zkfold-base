{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Algebra.EllipticCurve.Class where

import           Data.Functor                    ((<&>))
import           Data.Kind                       (Type)
import           Numeric.Natural                 (Natural)
import           Prelude                         hiding (Num (..), sum, (/), (^))
import           Test.QuickCheck                 hiding (scale)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.ByteString


data Point curve = Point { _x :: (BaseField curve), _y :: (BaseField curve) } | Inf

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

instance (EllipticCurve curve, Binary (BaseField curve)) => Binary (Point curve) where
    -- TODO: Point Compression
    -- When we know the equation of an elliptic curve, y^2 = x^3 + a * x + b
    -- then we only need to retain a flag sign byte,
    -- and the x-value to reconstruct the y-value of a point.
    put Inf         = putWord8 0
    put (Point x y) = putWord8 1 <> put x <> put y
    get = do
        flag <- getWord8
        if flag == 0 then return Inf
        else if flag == 1 then Point <$> get <*> get
        else fail ("Binary (Point curve): unexpected flag " <> show flag)

instance (EllipticCurve curve, Arbitrary (ScalarField curve)) => Arbitrary (Point curve) where
    arbitrary = arbitrary <&> (`mul` gen)

class (EllipticCurve curve1, EllipticCurve curve2, ScalarField curve1 ~ ScalarField curve2,
        Eq t, MultiplicativeGroup t, Exponent t (ScalarField curve1)) => Pairing curve1 curve2 t | curve1 curve2 -> t where
    pairing :: Point curve1 -> Point curve2 -> t

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
    => Eq (ScalarField curve)
    => ScalarField curve
    -> Point curve
    -> Point curve
pointMul = natScale . fromBinary . castBits . binaryExpansion
