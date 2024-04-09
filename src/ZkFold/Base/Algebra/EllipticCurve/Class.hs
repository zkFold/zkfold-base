{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module ZkFold.Base.Algebra.EllipticCurve.Class where

import           Data.Binary                     (Binary (..))
import           Data.Binary.Get                 (getWord8)
import           Data.Binary.Put                 (putWord8)
import           Data.Functor                    ((<&>))
import           Prelude                         hiding (Num (..), sum, (/), (^))
import qualified Prelude                         as Haskell
import           Test.QuickCheck                 hiding (scale)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Scale (BinScale (..))

type family BaseField curve

type family ScalarField curve

data Point curve = Point (BaseField curve) (BaseField curve) | Inf

class (FiniteField (BaseField curve), Eq (BaseField curve), Show (BaseField curve), Binary (BaseField curve),
      Haskell.Show (ScalarField curve), Haskell.Num (ScalarField curve), Haskell.Ord (ScalarField curve),
      PrimeField (ScalarField curve), Eq (ScalarField curve), BinaryExpansion (ScalarField curve), Arbitrary (ScalarField curve)
    ) => EllipticCurve curve where
    inf :: Point curve

    gen :: Point curve

    add :: Point curve -> Point curve -> Point curve

    mul :: ScalarField curve -> Point curve -> Point curve

instance EllipticCurve curve => Show (Point curve) where
    show Inf         = "Inf"
    show (Point x y) = "(" ++ show x ++ ", " ++ show y ++ ")"

instance EllipticCurve curve => Eq (Point curve) where
    Inf         == Inf         = True
    Inf         == _           = False
    _           == Inf         = False
    Point x1 y1 == Point x2 y2 = x1 == x2 && y1 == y2

instance EllipticCurve curve => AdditiveSemigroup (Point curve) where
    (+) = add

instance EllipticCurve curve => AdditiveMonoid (Point curve) where
    zero = Inf

instance EllipticCurve curve => AdditiveGroup (Point curve) where
    negate = pointNegate

instance EllipticCurve curve => Binary (Point curve) where
    put Inf = putWord8 0
    put (Point x y) = putWord8 1 <> put x <> put y
    get = do
      n <- getWord8
      if n == 0
        then return Inf
        else if n == 1 then do
            x <- get
            y <- get
            return (Point x y)
            else fail $
              "Binary (Point curve) get: expected flag bit 0 or 1 but saw "
              <> show n

instance EllipticCurve curve => Arbitrary (Point curve) where
    arbitrary = arbitrary <&> (`mul` gen)

class (EllipticCurve curve1, EllipticCurve curve2, ScalarField curve1 ~ ScalarField curve2,
        Eq t, MultiplicativeGroup t) => Pairing curve1 curve2 t | curve1 curve2 -> t where
    pairing :: Point curve1 -> Point curve2 -> t

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
    slope = (x * x + x * x + x * x) / (y + y)
    x' = slope * slope - x - x
    y' = slope * (x - x') - y

addPoints :: EllipticCurve curve => Point curve -> Point curve -> Point curve
addPoints p1 p2
    | p1 == p2  = pointDouble p1
    | otherwise = pointAdd p1 p2

pointNegate :: EllipticCurve curve => Point curve -> Point curve
pointNegate Inf         = Inf
pointNegate (Point x y) = Point x (negate y)

pointMul :: forall curve . EllipticCurve curve => ScalarField curve -> Point curve -> Point curve
pointMul n p = runBinScale $ n `scale` BinScale @(ScalarField curve) p
