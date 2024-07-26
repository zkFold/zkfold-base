{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters
{-# OPTIONS_GHC -Wno-orphans #-}
{-# LANGUAGE AllowAmbiguousTypes  #-}

module ZkFold.Symbolic.Data.Ed25519  where

import           Data.Void                                 (Void)
import           Prelude                                   (type (~), ($), (.))
import qualified Prelude                                   as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.EllipticCurve.Ed25519
import           ZkFold.Base.Control.HApplicative          (hliftA2)
import qualified ZkFold.Base.Data.Vector                   as V
import           ZkFold.Symbolic.Compiler                  hiding (forceZero)
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.UInt
import           ZkFold.Symbolic.Interpreter

zpToEd :: (Finite (Zp p)) => Point (Ed25519 UInt (Zp p)) -> Point (Ed25519 Void Void)
zpToEd Inf         = Inf
zpToEd (Point x y) = Point (toZp . toConstant $ x) (toZp . toConstant $ y)

edToZp :: (Finite (Zp p)) => Point (Ed25519 Void Void) -> Point (Ed25519 UInt (Zp p))
edToZp Inf         = Inf
edToZp (Point x y) = Point (fromConstant . fromZp $ x) (fromConstant . fromZp $ y)

-- | Ed25519 with @UInt 256 (Zp p)@ as computational backend
--
instance (Finite (Zp p)) => EllipticCurve (Ed25519 UInt (Zp p)) where
    type BaseField (Ed25519 UInt (Zp p)) = UInt 256 Auto (Interpreter (Zp p))
    type ScalarField (Ed25519 UInt (Zp p)) = UInt 256 Auto (Interpreter (Zp p))

    inf = Inf

    gen = Point
            (fromConstant (15112221349535400772501151409588531511454012693041857206046113283949847762202 :: Natural))
            (fromConstant (46316835694926478169428394003475163141307993866256225615783033603165251855960 :: Natural))

    -- | Addition casts point coordinates to @Zp Ed25519_Base@ and adds them as if they were points on @Ed25519 Void@
    --
    add p1 p2 = edToZp $ add (zpToEd p1) (zpToEd p2)

    -- | Multiplication casts point coordinates to @Zp Ed25519_Base@ and scale factor to @Zp Ed25519_Scalar@,
    --   then scales the point as if it were a point on @Ed25519 Void@
    --
    mul s p = edToZp @p $ mul (toZp . toConstant $ s) (zpToEd @p p)

instance
    ( SymbolicData a (UInt 256 Auto (ArithmeticCircuit a))
    , r ~ NumberOfRegisters a 256 Auto
    , KnownNat r
    , KnownNat (r + r)
    , 1 <= r
    ) => SymbolicData a (Point (Ed25519 ArithmeticCircuit a)) where

    type TypeSize a (Point (Ed25519 ArithmeticCircuit a)) =
        TypeSize a (UInt 256 Auto (ArithmeticCircuit a)) + TypeSize a (UInt 256 Auto (ArithmeticCircuit a))

    -- (0, 0) is never on a Twisted Edwards curve for any curve parameters.
    -- We can encode the point at infinity as (0, 0), therefore.
    pieces Inf         = hliftA2 V.append (pieces (zero :: UInt 256 Auto (ArithmeticCircuit a))) (pieces (zero :: UInt 256 Auto (ArithmeticCircuit a)))
    pieces (Point x y) = hliftA2 V.append (pieces x) (pieces y)

    restore c o = bool @(Bool (ArithmeticCircuit a)) @(Point (Ed25519 ArithmeticCircuit a)) (Point x y) Inf ((x == zero) && (y == zero))
        where
            (piecesX, piecesY) = V.splitAt @(TypeSize a (UInt 256 Auto (ArithmeticCircuit a))) o
            partialRestore = restore c
            (x, y) = (partialRestore piecesX, partialRestore piecesY)

instance (BoolType (Bool (c a)), Eq (Bool (c a)) (BaseField (Ed25519 c a))) => Eq (Bool (c a)) (Point (Ed25519 c a)) where
    Inf == Inf                     = true
    Inf == _                       = false
    _ == Inf                       = false
    (Point x1 y1) == (Point x2 y2) = x1 == x2 && y1 == y2

    Inf /= Inf                     = false
    Inf /= _                       = true
    _ /= Inf                       = true
    (Point x1 y1) /= (Point x2 y2) = x1 /= x2 || y1 /= y2

-- | Ed25519 with @UInt 256 ArithmeticCircuit a@ as computational backend
--
instance
    ( Arithmetic a
    , SymbolicData a (UInt 256 Auto (ArithmeticCircuit a))
    , FromConstant Natural (UInt 512 Auto (ArithmeticCircuit a))
    , EuclideanDomain (UInt 512 Auto (ArithmeticCircuit a))
    , r256 ~ NumberOfRegisters a 256 Auto
    , KnownNat r256
    , KnownNat (r256 + r256)
    , 1 <= r256
    , r512 ~ NumberOfRegisters a 512 Auto
    , 1 <= r512
    , KnownNat r512
    , KnownNat (r512 + r512 + r512)
    , Iso (UInt 256 Auto (ArithmeticCircuit a)) (ByteString 256 (ArithmeticCircuit a))
    ) => EllipticCurve (Ed25519 ArithmeticCircuit a)  where

    type BaseField (Ed25519 ArithmeticCircuit a) = UInt 256 Auto (ArithmeticCircuit a)
    type ScalarField (Ed25519 ArithmeticCircuit a) = UInt 256 Auto (ArithmeticCircuit a)

    inf = Inf

    gen = Point
            (fromConstant (15112221349535400772501151409588531511454012693041857206046113283949847762202 :: Natural))
            (fromConstant (46316835694926478169428394003475163141307993866256225615783033603165251855960 :: Natural))

    add x y = bool @(Bool (ArithmeticCircuit a)) @(Point (Ed25519 ArithmeticCircuit a)) (acAdd25519 x y) (acDouble25519 x) (x == y)

    -- pointMul uses natScale which converts the scale to Natural.
    -- We can't convert arithmetic circuits to Natural, so we can't use pointMul either.
    --
    mul sc x = sum $ P.zipWith (\b p -> bool @(Bool (ArithmeticCircuit a)) zero p (isSet bits b)) [255, 254 .. 0] (P.iterate (\e -> e + e) x)
        where
            bits :: ByteString 256 (ArithmeticCircuit a)
            bits = from sc

acAdd25519
    :: forall a r
    .  Arithmetic a
    => EuclideanDomain (UInt 512 Auto (ArithmeticCircuit a))
    => r ~ NumberOfRegisters a 512 Auto
    => KnownNat r
    => KnownNat (r + r + r)
    => 1 <= r
    => Point (Ed25519 ArithmeticCircuit a)
    -> Point (Ed25519 ArithmeticCircuit a)
    -> Point (Ed25519 ArithmeticCircuit a)
acAdd25519 Inf q = q
acAdd25519 p Inf = p
acAdd25519 (Point x1 y1) (Point x2 y2) = Point (shrink x3) (shrink y3)
    where
        -- We will perform multiplications of UInts of up to n bits, therefore we need 2n bits to store the result.
        --
        x1e, y1e, x2e, y2e :: UInt 512 Auto (ArithmeticCircuit a)
        x1e = extend x1
        y1e = extend y1
        x2e = extend x2
        y2e = extend y2

        m :: UInt 512 Auto (ArithmeticCircuit a)
        m = fromConstant $ value @Ed25519_Base

        plusM :: UInt 512 Auto (ArithmeticCircuit a) -> UInt 512 Auto (ArithmeticCircuit a) -> UInt 512 Auto (ArithmeticCircuit a)
        plusM x y = (x + y) `mod` m

        mulM :: UInt 512 Auto (ArithmeticCircuit a) -> UInt 512 Auto (ArithmeticCircuit a) -> UInt 512 Auto (ArithmeticCircuit a)
        mulM x y = (x * y) `mod` m

        d :: UInt 512 Auto (ArithmeticCircuit a)
        d = fromConstant $ fromZp @Ed25519_Base $ (toZp (-121665) // toZp 121666)

        x3n :: UInt 512 Auto (ArithmeticCircuit a)
        x3n = (x1e `mulM` y2e) `plusM` (y1e `mulM` x2e)

        x3d :: UInt 512 Auto (ArithmeticCircuit a)
        x3d = one `plusM` (d `mulM` x1e `mulM` x2e `mulM` y1e `mulM` y2e)

        -- Calculate the modular inverse using Extended Euclidean algorithm
        x3di :: UInt 512 Auto (ArithmeticCircuit a)
        (x3di, _, _) = eea x3d m


        x3 :: UInt 512 Auto (ArithmeticCircuit a)
        x3 = x3n `mulM` x3di

        y3n :: UInt 512 Auto (ArithmeticCircuit a)
        y3n = (y1e `mulM` y2e) `plusM` (x1e `mulM` x2e)

        y3d :: UInt 512 Auto (ArithmeticCircuit a)
        y3d = one `plusM` ((m - d) `mulM` x1e `mulM` x2e `mulM` y1e `mulM` y2e)

        -- Calculate the modular inverse using Extended Euclidean algorithm
        y3di :: UInt 512 Auto (ArithmeticCircuit a)
        (y3di, _, _) = eea y3d m

        y3 :: UInt 512 Auto (ArithmeticCircuit a)
        y3 = y3n `mulM` y3di

acDouble25519
    :: forall a r
    .  Arithmetic a
    => EuclideanDomain (UInt 512 Auto (ArithmeticCircuit a))
    => r ~ NumberOfRegisters a 512 Auto
    => KnownNat r
    => KnownNat (r + r + r)
    => 1 <= r
    => Point (Ed25519 ArithmeticCircuit a)
    -> Point (Ed25519 ArithmeticCircuit a)
acDouble25519 Inf = Inf
acDouble25519 (Point x1 y1) = Point (shrink x3) (shrink y3)
    where
        -- We will perform multiplications of UInts of up to n bits, therefore we need 2n bits to store the result.
        --
        xe, ye :: UInt 512 Auto (ArithmeticCircuit a)
        xe = extend x1
        ye = extend y1

        m :: UInt 512 Auto (ArithmeticCircuit a)
        m = fromConstant $ value @Ed25519_Base

        plusM :: UInt 512 Auto (ArithmeticCircuit a) -> UInt 512 Auto (ArithmeticCircuit a) -> UInt 512 Auto (ArithmeticCircuit a)
        plusM x y = (x + y) `mod` m

        mulM :: UInt 512 Auto (ArithmeticCircuit a) -> UInt 512 Auto (ArithmeticCircuit a) -> UInt 512 Auto (ArithmeticCircuit a)
        mulM x y = (x * y) `mod` m


        x3n :: UInt 512 Auto (ArithmeticCircuit a)
        x3n = (xe `mulM` ye) `plusM` (xe `mulM` ye)

        x3d :: UInt 512 Auto (ArithmeticCircuit a)
        x3d = ((m - one) `mulM` xe `mulM` xe) `plusM` (ye `mulM` ye)

        -- Calculate the modular inverse using Extended Euclidean algorithm
        x3di :: UInt 512 Auto (ArithmeticCircuit a)
        (x3di, _, _) = eea x3d m

        x3 :: UInt 512 Auto (ArithmeticCircuit a)
        x3 = x3n `mulM` x3di


        y3n :: UInt 512 Auto (ArithmeticCircuit a)
        y3n = (ye `mulM` ye) `plusM` (xe `mulM` xe)

        y3d :: UInt 512 Auto (ArithmeticCircuit a)
        y3d = (one + one) `plusM` (xe `mulM` xe) `plusM` ((m - one) `mulM` ye `mulM` ye)

        -- Calculate the modular inverse using Extended Euclidean algorithm
        y3di :: UInt 512 Auto (ArithmeticCircuit a)
        (y3di, _, _) = eea y3d m

        y3 :: UInt 512 Auto (ArithmeticCircuit a)
        y3 = y3n `mulM` y3di
