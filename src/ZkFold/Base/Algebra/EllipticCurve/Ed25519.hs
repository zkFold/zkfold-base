{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Algebra.EllipticCurve.Ed25519  where

import           Data.Void                               (Void)
import           Prelude                                 (otherwise, ($), (==))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class

-- | The Ed25519 curve used in EdDSA signature scheme.
-- @c@ represents the "computational context" used to store and perform operations on curve points.
--
data Ed25519 c 

-- | 2^252 + 27742317777372353535851937790883648493 is the order of the multiplicative group in Ed25519
-- with the generator point defined below in @instance EllipticCurve (Ed25519 Void r)@
--
type Ed25519_Scalar = 7237005577332262213973186563042994240857116359379907606001950938285454250989
instance Prime Ed25519_Scalar

-- | 2^255 - 19 is the order of the base field from which point coordinates are taken.
--
type Ed25519_Base = 57896044618658097711785492504343953926634992332820282019728792003956564819949
instance Prime Ed25519_Base

-- | The purely mathematical implementation of Ed25519.
-- It is available for use as-is and serves as "backend" for the @UInt 256 (Zp p)@ implementation as well.
--
instance EllipticCurve (Ed25519 Void) where
    type BaseField (Ed25519 Void) = Zp Ed25519_Base
    type ScalarField (Ed25519 Void) = Zp Ed25519_Scalar

    inf = Inf

    gen = Point
            (toZp @Ed25519_Base $ 15112221349535400772501151409588531511454012693041857206046113283949847762202)
            (toZp @Ed25519_Base $ 46316835694926478169428394003475163141307993866256225615783033603165251855960)

    add p1 p2
      | p1 == p2  = ed25519Double p1
      | otherwise = ed25519Add p1 p2

    mul = pointMul


ed25519Add :: Point (Ed25519 Void) -> Point (Ed25519 Void) -> Point (Ed25519 Void)
ed25519Add p Inf = p
ed25519Add Inf q = q
ed25519Add (Point x1 y1) (Point x2 y2) = Point x3 y3
    where
        d :: BaseField (Ed25519 Void)
        d = negate $ toZp 121665 // toZp 121666

        a :: BaseField (Ed25519 Void)
        a = negate $ toZp 1

        x3 = (x1 * y2 + y1 * x2) // (toZp 1 + d * x1 * x2 * y1 * y2)
        y3 = (y1 * y2 - a * x1 * x2) // (toZp 1 - d * x1 * x2 * y1 * y2)

ed25519Double :: Point (Ed25519 Void) -> Point (Ed25519 Void)
ed25519Double Inf = Inf
ed25519Double (Point x y) = Point x3 y3
    where
        a :: BaseField (Ed25519 Void)
        a = negate $ toZp 1

        x3 = 2 * x * y // (a * x * x + y * y)
        y3 = (y * y - a * x * x) // (toZp 2 - a * x * x - y * y)
