{-# LANGUAGE TypeOperators #-}

module ZkFold.Base.Algebra.EllipticCurve.Pairing (ate) where

import           Data.Bits                               (shiftR)
import           Data.Bool                               (Bool, otherwise, (&&))
import           Data.Eq                                 (Eq, (==))
import           Data.Function                           (($))
import           Data.List                               (reverse, tail, unfoldr)
import           Data.Maybe                              (Maybe (..))
import           Data.Ord                                ((<=))
import           Data.Type.Equality                      (type (~))
import           Numeric.Natural                         (Natural)
import           Prelude                                 (Integer, error, even, odd)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field         (Ext2 (..), Ext3 (..))
import           ZkFold.Base.Algebra.EllipticCurve.Class

-- Adapted from:
-- https://github.com/nccgroup/pairing-bls12381/blob/master/Crypto/Pairing_bls12381.hs

type Untwisted c i1 i2 = Ext2 (Ext3 (BaseField c) i1) i2

-- Untwist point on E2 for pairing calculation
untwist ::
  (Field (BaseField c), Untwisted c i1 i2 ~ g, Field g) => Point c -> (g, g)
untwist (Point x1 y1) = (wideX, wideY)
  where
    root = Ext3 zero one zero
    wideX = Ext2 zero (Ext3 zero zero x1) // Ext2 zero root
    wideY = Ext2 zero (Ext3 zero zero y1) // Ext2 root zero
untwist Inf = error "untwist: point at infinity"

-- Used in miller loop for computing line functions l_r,r and v_2r
doubleEval ::
  Field (BaseField c2) => Untwisted c2 i1 i2 ~ g =>
  FromConstant (BaseField c1) g => Field g =>
  Point c2 -> Point c1 -> g
doubleEval r (Point px py) = fromConstant py - (fromConstant px * slope) - v
  where
    (rx, ry) = untwist r
    slope = (rx * rx + rx * rx + rx * rx) // (ry + ry)
    v = ry - slope * rx
doubleEval _ Inf = error "doubleEval: point at infinity"

-- Used in miller loop for computer line function l_r,p and v_r+p
addEval ::
  (BaseField c2 ~ f, Field f, Eq f) =>
  (Untwisted c2 i1 i2 ~ g, FromConstant (BaseField c1) g, Field g) =>
  Point c2 -> Point c2 -> Point c1 -> g
addEval r q p@(Point px _) = if (rx == qx) && (ry + qy == zero)
                then fromConstant px - rx
                else addEval' (rx, ry) (qx, qy) p
  where
    (rx, ry) = untwist r
    (qx, qy) = untwist q
addEval _ _ Inf = error "addEval: point at infinity"

-- Helper function for addEval
addEval' ::
  (FromConstant (BaseField c) g, Field g) => (g, g) -> (g, g) -> Point c -> g
addEval' (rx, ry) (qx, qy) (Point px py) =
  fromConstant py - (fromConstant px * slope) - v
  where
    slope = (qy - ry) // (qx - rx)
    v = ((qy * rx) - (ry * qx)) // (rx - qx)
addEval' _ _ Inf = error "addEval': point at infinity"

-- Classic Miller loop for Ate pairing
miller ::
  (BaseField c2 ~ f, Field f, Eq f) =>
  (Untwisted c2 i1 i2 ~ g, FromConstant (BaseField c1) g, Field g) =>
  Point c1 -> Point c2 -> g
miller p q = miller' p q q iterations one
  where
    iterations = tail $ reverse $  -- list of true/false per bits of operand
      unfoldr (\b -> if b == (0 :: Integer) then Nothing
                     else Just(odd b, shiftR b 1)) 0xd201000000010000

-- Double and add loop helper for Miller (iterative)
miller' ::
  (BaseField c2 ~ f, Field f, Eq f) =>
  (Untwisted c2 i1 i2 ~ g, FromConstant (BaseField c1) g, Field g) =>
  Point c1 -> Point c2 -> Point c2 -> [Bool] -> g -> g
miller' _ _ _ [] result = result
miller' p q r (i:iters) result =
  if i then miller' p q (pointAdd doubleR q) iters (accum * addEval doubleR q p)
       else miller' p q doubleR iters accum
  where
    accum = result * result * doubleEval r p
    doubleR = pointDouble r

-- | Pairing calculation for a valid point in G1 and another valid point in G2.
-- Classic Ate pairing.
ate ::
  forall c1 c2 i1 i2 f g.
  (Finite (ScalarField c2), BaseField c2 ~ f, FiniteField f, Eq f) =>
  (Untwisted c2 i1 i2 ~ g, FromConstant (BaseField c1) g, Field g) =>
  Point c1 -> Point c2 -> g
ate Inf _ = zero
ate _ Inf = zero
ate p1 p2 = pow' (miller p1 p2) ((p ^ (12 :: Natural) -! 1) `div` r) one
  where
    p = order @(BaseField c2)
    r = order @(ScalarField c2)

-- Used for the final exponentiation; opportunity for further perf optimization
pow' :: MultiplicativeSemigroup a => a -> Natural -> a -> a
pow' a0 e result
  | e <= 1    = a0
  | even e    = accum2
  | otherwise = accum2 * a0
  where
    accum  = pow' a0 (shiftR e 1) result
    accum2 = accum * accum
