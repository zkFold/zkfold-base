module ZkFold.Base.Algebra.EllipticCurve.Class where

import           Prelude                         hiding (Num(..), (/))
import qualified Prelude                         as Haskell

import           ZkFold.Base.Algebra.Basic.Class

type family BaseField curve

type family ScalarField curve

data Point curve = Point (BaseField curve) (BaseField curve) | Inf

class (FiniteField (BaseField curve), Haskell.Num (BaseField curve), Eq (BaseField curve)) => EllipticCurve curve where
    inf :: Point curve

    gen :: Point curve

    add :: Point curve -> Point curve -> Point curve

    mul :: ScalarField curve -> Point curve -> Point curve

instance EllipticCurve curve => Eq (Point curve) where
    Inf == Inf = True
    Inf == _   = False
    _   == Inf = False
    Point x1 y1 == Point x2 y2 = x1 == x2 && y1 == y2

pointAdd :: EllipticCurve curve => Point curve -> Point curve -> Point curve
pointAdd p   Inf     = p
pointAdd Inf q       = q
pointAdd (Point x1 y1) (Point x2 y2)
  | x1 == x2  = Inf
  | otherwise = Point x3 y3
  where
    slope  = (y1 - y2) / (x1 - x2)
    x3 = slope * slope - x1 - x2
    y3 = slope * (x1 - x3) - y1

pointDouble :: EllipticCurve curve => Point curve -> Point curve
pointDouble Inf = Inf
pointDouble (Point x y) = Point x' y'
  where
    slope = (3 * x * x) / (2 * y)
    x' = slope * slope - x - x
    y' = slope * (x - x') - y

pointNegate :: EllipticCurve curve => Point curve -> Point curve
pointNegate Inf = Inf
pointNegate (Point x y) = Point x (negate y)

pointMul :: EllipticCurve curve => Integer -> Point curve -> Point curve
pointMul n p
  | n < 0     = pointNegate $ pointMul (negate n) p
  | n == 0    = Inf
  | n == 1    = p
  | even n    = p'
  | otherwise = pointAdd p p'
  where
    p' = pointMul (n `div` 2) (pointDouble p)