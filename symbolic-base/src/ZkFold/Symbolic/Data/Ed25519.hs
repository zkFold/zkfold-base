{-# LANGUAGE RebindableSyntax     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Symbolic.Data.Ed25519 (AcEd25519) where

import           Control.DeepSeq                           (NFData, force)
import           Prelude                                   (fromInteger, type (~), ($))
import qualified Prelude                                   as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.EllipticCurve.Ed25519
import qualified ZkFold.Base.Data.Vector                   as V
import qualified ZkFold.Symbolic.Class                     as S
import           ZkFold.Symbolic.Class                     (Symbolic)
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq
import           ZkFold.Symbolic.Data.FFA
import           ZkFold.Symbolic.Data.FieldElement

data AcEd25519 c

-- | Ed25519 with @UInt 256 ArithmeticCircuit a@ as computational backend
--
instance
    ( Symbolic c
    , NFData (c (V.Vector Size))
    ) => EllipticCurve (AcEd25519 c)  where

    type BaseField (AcEd25519 c) = FFA Ed25519_Base c
    type ScalarField (AcEd25519 c) = FieldElement c
    type BooleanOf (AcEd25519 c) = Bool c

    gen = point
            (fromConstant (15112221349535400772501151409588531511454012693041857206046113283949847762202 :: Natural))
            (fromConstant (46316835694926478169428394003475163141307993866256225615783033603165251855960 :: Natural))

    add x y = if x == y then acDouble25519 x else acAdd25519 x y

    -- pointMul uses natScale which converts the scale to Natural.
    -- We can't convert arithmetic circuits to Natural, so we can't use pointMul either.
    --
    mul = scale

instance
    ( EllipticCurve c
    , SymbolicData (Point c)
    , l ~ Layout (Point c)
    , ctx ~ Context (Point c)
    , Symbolic ctx
    , a ~ S.BaseField ctx
    , bits ~ NumberOfBits a
    , BooleanOf c ~ Bool ctx
    ) => Scale (FieldElement ctx) (Point c) where

    scale sc x = sum $ P.zipWith (\b p -> bool @(Bool ctx) zero p (isSet bits b)) [upper, upper -! 1 .. 0] (P.iterate (\e -> e + e) x)
        where
            bits :: ByteString bits ctx
            bits = ByteString $ binaryExpansion sc

            upper :: Natural
            upper = value @bits -! 1

a :: Symbolic ctx => FFA Ed25519_Base ctx
a = fromConstant @P.Integer (-1)

d :: Symbolic ctx => FFA Ed25519_Base ctx
d = fromConstant @P.Integer (-121665) // fromConstant @Natural 121666

acAdd25519
    :: forall c
    .  Symbolic c
    => NFData (c (V.Vector Size))
    => Point (AcEd25519 c)
    -> Point (AcEd25519 c)
    -> Point (AcEd25519 c)
acAdd25519 p@(Point x1 y1 isInf1) q@(Point x2 y2 isInf2) =
    if isInf1 then q
    else if isInf2 then p
    else point x3 y3
    where
        prodx = x1 * x2
        prody = y1 * y2
        prod4 = d * prodx * prody
        x3 = force $ (x1 * y2 + y1 * x2) // (one + prod4)
        y3 = force $ (prody - a * prodx) // (one - prod4)

acDouble25519
    :: forall c
    .  Symbolic c
    => NFData (c (V.Vector Size))
    => Point (AcEd25519 c)
    -> Point (AcEd25519 c)
acDouble25519 (Point x1 y1 isInf) =
    if isInf then inf else point x3 y3
    where
        xsq = x1 * x1
        ysq = y1 * y1
        xy =  x1 * y1

        -- Note: due to our laws for finv, division below is going to work exactly as it should
        -- if the point is (0, 0)
        x3 = force $ (xy + xy) // (a * xsq + ysq)
        y3 = force $ (ysq - a * xsq) // (one + one - a * xsq  - ysq)

