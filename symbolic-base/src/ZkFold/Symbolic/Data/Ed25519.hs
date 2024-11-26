{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Symbolic.Data.Ed25519 () where

import           Control.DeepSeq                           (NFData, force)
import           Data.Functor.Rep                          (Representable)
import           Data.Traversable                          (Traversable)
import           Prelude                                   (type (~), ($))
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


instance
    ( Symbolic c
    , S.BaseField c ~ a
    ) => SymbolicData (Point (Ed25519 c)) where

    type Context (Point (Ed25519 c)) = c
    type Support (Point (Ed25519 c)) = Support (FFA Ed25519_Base c)
    type Layout (Point (Ed25519 c)) = Layout (FFA Ed25519_Base c, FFA Ed25519_Base c)
    type Payload (Point (Ed25519 c)) = Payload (FFA Ed25519_Base c, FFA Ed25519_Base c)

    -- (0, 0) is never on a Twisted Edwards curve for any curve parameters.
    -- We can encode the point at infinity as (0, 0), therefore.
    -- Moreover, (0, 0) acts as the point at infinity when used in the addition formula.
    -- We can restore Inf as (0, 0) since we can't arithmetise sum-types.
    -- It will need additional checks in pointDouble because of the denominator becoming zero, though.
    -- TODO: Think of a better solution
    --
    arithmetize Inf         = arithmetize (zero :: FFA Ed25519_Base c, zero :: FFA Ed25519_Base c)
    arithmetize (Point x y) = arithmetize (x, y)
    payload Inf         = payload (zero :: FFA Ed25519_Base c, zero :: FFA Ed25519_Base c)
    payload (Point x y) = payload (x, y)
    restore f = Point x y
        where
            (x, y) = restore f

instance (Symbolic c) => Eq (Bool c) (Point (Ed25519 c)) where
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
    ( Symbolic c
    , NFData (c (V.Vector Size))
    ) => EllipticCurve (Ed25519 c)  where

    type BaseField (Ed25519 c) = FFA Ed25519_Base c
    type ScalarField (Ed25519 c) = FieldElement c

    inf = Inf

    gen = Point
            (fromConstant (15112221349535400772501151409588531511454012693041857206046113283949847762202 :: Natural))
            (fromConstant (46316835694926478169428394003475163141307993866256225615783033603165251855960 :: Natural))

    add x y = bool @(Bool c) @(Point (Ed25519 c)) (acAdd25519 x y) (acDouble25519 x) (x == y)

    -- pointMul uses natScale which converts the scale to Natural.
    -- We can't convert arithmetic circuits to Natural, so we can't use pointMul either.
    --
    mul = scale

instance
    ( EllipticCurve c
    , SymbolicData (Point c)
    , l ~ Layout (Point c)
    , Representable l
    , Traversable l
    , Representable (Payload (Point c))
    , ctx ~ Context (Point c)
    , Symbolic ctx
    , a ~ S.BaseField ctx
    , bits ~ NumberOfBits a
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
    => Point (Ed25519 c)
    -> Point (Ed25519 c)
    -> Point (Ed25519 c)
acAdd25519 Inf q = q
acAdd25519 p Inf = p
acAdd25519 (Point x1 y1) (Point x2 y2) = Point x3 y3
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
    => Point (Ed25519 c)
    -> Point (Ed25519 c)
acDouble25519 Inf = Inf
acDouble25519 (Point x1 y1) = Point x3 y3
    where
        xsq = x1 * x1
        ysq = y1 * y1
        xy =  x1 * y1

        -- Note: due to our laws for finv, division below is going to work exactly as it should
        -- if the point is (0, 0)
        x3 = force $ (xy + xy) // (a * xsq + ysq)
        y3 = force $ (ysq - a * xsq) // (one + one - a * xsq  - ysq)

