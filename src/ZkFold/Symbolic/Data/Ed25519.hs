{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Symbolic.Data.Ed25519  where

import           Data.Void                                 (Void)
import           GHC.Generics                              (Generic1, Generically1 (..))
import           GHC.TypeNats                              (Natural)
import           Prelude                                   (($), (.), (<>))
import qualified Prelude                                   as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Basic.VectorSpace
import qualified ZkFold.Base.Algebra.EllipticCurve.Class   as Base
import qualified ZkFold.Base.Algebra.EllipticCurve.Ed25519 as Base
import           ZkFold.Symbolic.Compiler                  hiding (forceZero)
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Compare
import           ZkFold.Symbolic.Data.UInt

data PointEd25519 a = PointEd25519 (UInt 256 a) (UInt 256 a)
  deriving stock (P.Eq, P.Functor, P.Foldable, P.Traversable, Generic1)
deriving via Generically1 PointEd25519 instance FiniteField a => VectorSpace a PointEd25519
instance (DiscreteField a, FiniteField a) => Eq a PointEd25519
instance (TrichotomyField a, FiniteField a) => Ord a PointEd25519
instance FiniteField (Zp p) => AdditiveSemigroup (PointEd25519 (Zp p)) where (+) = add
instance FiniteField (Zp p) => AdditiveMonoid (PointEd25519 (Zp p)) where zero = inf
instance
  ( EuclideanDomain (UInt 512 (ArithmeticCircuit a))
  , BinaryExpansion (UInt 256 (ArithmeticCircuit a))
  , Arithmetic a
  ) => AdditiveSemigroup (PointEd25519 (ArithmeticCircuit a)) where
    (+) = add
instance
  ( EuclideanDomain (UInt 512 (ArithmeticCircuit a))
  , BinaryExpansion (UInt 256 (ArithmeticCircuit a))
  , Arithmetic a
  ) => AdditiveMonoid (PointEd25519 (ArithmeticCircuit a)) where
    zero = inf

inf :: AdditiveMonoid (UInt 256 a) => PointEd25519 a
inf = PointEd25519 zero zero

gen :: forall a. FromConstant Natural (UInt 256 a) => PointEd25519 a
gen = PointEd25519
    (fromConstant @Natural @(UInt 256 a) (15112221349535400772501151409588531511454012693041857206046113283949847762202))
    (fromConstant @Natural @(UInt 256 a) (46316835694926478169428394003475163141307993866256225615783033603165251855960))

isInf :: (P.Eq a, AdditiveMonoid (UInt 256 a)) => PointEd25519 a -> P.Bool
isInf (PointEd25519 x y) = x P.== zero P.&& y P.== zero

zpToEd :: (P.Eq a, AdditiveMonoid (UInt 256 a), ToConstant (UInt 256 a) P.Integer) => PointEd25519 a -> Base.Point (Base.Ed25519 Void)
zpToEd pt | isInf pt        = Base.Inf
zpToEd (PointEd25519 x y)   = Base.Point (toZp . toConstant $ x) (toZp . toConstant $ y)

edToZp :: (AdditiveMonoid (UInt 256 a), FiniteField a) => Base.Point (Base.Ed25519 Void) -> PointEd25519 a
edToZp Base.Inf         = PointEd25519 zero zero
edToZp (Base.Point x y) = PointEd25519 (fromConstant . fromZp $ x) (fromConstant . fromZp $ y)

class EllipticCurveEd25519 a where
    add :: PointEd25519 a -> PointEd25519 a -> PointEd25519 a
    mul :: UInt 256 a -> PointEd25519 a -> PointEd25519 a

-- | Ed25519 with @UInt 256 (Zp p)@ as computational backend
--
instance FiniteField (Zp p) => EllipticCurveEd25519 (Zp p) where

    -- | Addition casts point coordinates to @Zp Ed25519_Base@ and adds them as if they were points on @Ed25519 Void@
    --
    add p1 p2 = edToZp $ Base.add (zpToEd p1) (zpToEd p2)

    -- | Multiplication casts point coordinates to @Zp Ed25519_Base@ and scale factor to @Zp Ed25519_Scalar@,
    --   then scales the point as if it were a point on @Ed25519 Void@
    --
    mul s p = edToZp $ Base.mul (toZp . toConstant $ s) (zpToEd p)

-- | Ed25519 with @UInt 256 (ArithmeticCircuit a)@ as computational backend
--
instance
    ( Arithmetic a
    , EuclideanDomain (UInt 512 (ArithmeticCircuit a))
    , BinaryExpansion (UInt 256 (ArithmeticCircuit a))
    ) => EllipticCurveEd25519 (ArithmeticCircuit a) where

    add x y = bool (acAdd25519 x y) (acDouble25519 x) (x == y)

    -- pointMul uses natScale which converts the scale to Natural.
    -- We can't convert arithmetic circuits to Natural, so we can't use pointMul either.
    --
    mul sc x = bitsMul (uintBits sc) x
        where
            bitsMul :: [ArithmeticCircuit a] -> PointEd25519 (ArithmeticCircuit a) -> PointEd25519 (ArithmeticCircuit a)
            bitsMul bits pt = sum $ P.zipWith scaleV bits (P.iterate (\e -> e + e) pt)

            uintBits :: UInt 256 (ArithmeticCircuit a) -> [ArithmeticCircuit a]
            uintBits (UInt lows hi) = P.concatMap binaryExpansion lows <> binaryExpansion hi

acAdd25519
    :: forall a
    .  Arithmetic a
    => EuclideanDomain (UInt 512 (ArithmeticCircuit a))
    => PointEd25519 (ArithmeticCircuit a)
    -> PointEd25519 (ArithmeticCircuit a)
    -> PointEd25519 (ArithmeticCircuit a)
-- acAdd25519 Inf q = q
-- acAdd25519 p Inf = p
acAdd25519 (PointEd25519 x1 y1) (PointEd25519 x2 y2) = PointEd25519 (shrink x3) (shrink y3)
    where
        -- We will perform multiplications of UInts of up to n bits, therefore we need 2n bits to store the result.
        --
        x1e, y1e, x2e, y2e :: UInt 512 (ArithmeticCircuit a)
        x1e = extend x1
        y1e = extend y1
        x2e = extend x2
        y2e = extend y2

        m :: UInt 512 (ArithmeticCircuit a)
        m = fromConstant $ value @Base.Ed25519_Base

        plusM :: UInt 512 (ArithmeticCircuit a) -> UInt 512 (ArithmeticCircuit a) -> UInt 512 (ArithmeticCircuit a)
        plusM x y = (x + y) `mod` m

        mulM :: UInt 512 (ArithmeticCircuit a) -> UInt 512 (ArithmeticCircuit a) -> UInt 512 (ArithmeticCircuit a)
        mulM x y = (x * y) `mod` m

        d :: UInt 512 (ArithmeticCircuit a)
        d = fromConstant $ fromZp @Base.Ed25519_Base $ (toZp (-121665) // (toZp 121666))

        x3n :: UInt 512 (ArithmeticCircuit a)
        x3n = (x1e `mulM` y2e) `plusM` (y1e `mulM` x2e)

        x3d :: UInt 512 (ArithmeticCircuit a)
        x3d = one `plusM` (d `mulM` x1e `mulM` x2e `mulM` y1e `mulM` y2e)

        -- Calculate the modular inverse using Extended Euclidean algorithm
        x3di :: UInt 512 (ArithmeticCircuit a)
        (x3di, _, _) = eea x3d m


        x3 :: UInt 512 (ArithmeticCircuit a)
        x3 = x3n `mulM` x3di

        y3n :: UInt 512 (ArithmeticCircuit a)
        y3n = (y1e `mulM` y2e) `plusM` (x1e `mulM` x2e)

        y3d :: UInt 512 (ArithmeticCircuit a)
        y3d = one `plusM` ((m - d) `mulM` x1e `mulM` x2e `mulM` y1e `mulM` y2e)

        -- Calculate the modular inverse using Extended Euclidean algorithm
        y3di :: UInt 512 (ArithmeticCircuit a)
        (y3di, _, _) = eea y3d m

        y3 :: UInt 512 (ArithmeticCircuit a)
        y3 = y3n `mulM` y3di

acDouble25519
    :: forall a
    .  Arithmetic a
    => EuclideanDomain (UInt 512 (ArithmeticCircuit a))
    => PointEd25519 (ArithmeticCircuit a)
    -> PointEd25519 (ArithmeticCircuit a)
acDouble25519 (PointEd25519 x1 y1) =
    ifThenElse
      (x1 == zero && y1 == zero) -- point at infinity
      inf
      (PointEd25519 (shrink x3) (shrink y3))
    where
        -- We will perform multiplications of UInts of up to n bits, therefore we need 2n bits to store the result.
        --
        xe, ye :: UInt 512 (ArithmeticCircuit a)
        xe = extend x1
        ye = extend y1

        m :: UInt 512 (ArithmeticCircuit a)
        m = fromConstant $ value @Base.Ed25519_Base

        plusM :: UInt 512 (ArithmeticCircuit a) -> UInt 512 (ArithmeticCircuit a) -> UInt 512 (ArithmeticCircuit a)
        plusM x y = (x + y) `mod` m

        mulM :: UInt 512 (ArithmeticCircuit a) -> UInt 512 (ArithmeticCircuit a) -> UInt 512 (ArithmeticCircuit a)
        mulM x y = (x * y) `mod` m


        x3n :: UInt 512 (ArithmeticCircuit a)
        x3n = (xe `mulM` ye) `plusM` (xe `mulM` ye)

        x3d :: UInt 512 (ArithmeticCircuit a)
        x3d = ((m - one) `mulM` xe `mulM` xe) `plusM` (ye `mulM` ye)

        -- Calculate the modular inverse using Extended Euclidean algorithm
        x3di :: UInt 512 (ArithmeticCircuit a)
        (x3di, _, _) = eea x3d m

        x3 :: UInt 512 (ArithmeticCircuit a)
        x3 = x3n `mulM` x3di


        y3n :: UInt 512 (ArithmeticCircuit a)
        y3n = (ye `mulM` ye) `plusM` (xe `mulM` xe)

        y3d :: UInt 512 (ArithmeticCircuit a)
        y3d = (one + one) `plusM` (xe `mulM` xe) `plusM` ((m - one) `mulM` ye `mulM` ye)

        -- Calculate the modular inverse using Extended Euclidean algorithm
        y3di :: UInt 512 (ArithmeticCircuit a)
        (y3di, _, _) = eea y3d m

        y3 :: UInt 512 (ArithmeticCircuit a)
        y3 = y3n `mulM` y3di
