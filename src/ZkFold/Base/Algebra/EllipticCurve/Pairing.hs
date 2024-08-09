{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Base.Algebra.EllipticCurve.Pairing
  ( millerLoop
  , finalExponentiation
  ) where

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
-- https://github.com/sdiehl/pairing/blob/master/src/Data/Pairing/Ate.hs

type Untwisted c i1 i2 = Ext2 (Ext3 (BaseField c) i1) i2

-- Untwist point on E2 for pairing calculation
-- FIXME: this works for BLS12-381 only
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
millerLoop ::
  (BaseField c2 ~ f, Field f, Eq f) =>
  (Untwisted c2 i1 i2 ~ g, FromConstant (BaseField c1) g, Field g) =>
  Integer -> Point c1 -> Point c2 -> g
millerLoop param p q = miller' p q q iterations one
  where
    iterations = tail $ reverse $  -- list of true/false per bits of operand
      unfoldr (\b -> if b == (0 :: Integer) then Nothing
                     else Just(odd b, shiftR b 1)) param

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

finalExponentiation ::
  forall c a.
  (Finite (ScalarField c), Finite (BaseField c), MultiplicativeMonoid a) =>
  a -> a
finalExponentiation x = pow' x ((p ^ (12 :: Natural) -! 1) `div` r) one
  where
    p = order @(BaseField c)
    r = order @(ScalarField c)

-- Used for the final exponentiation; opportunity for further perf optimization
pow' :: MultiplicativeSemigroup a => a -> Natural -> a -> a
pow' a0 e result
  | e <= 1    = a0
  | even e    = accum2
  | otherwise = accum2 * a0
  where
    accum  = pow' a0 (shiftR e 1) result
    accum2 = accum * accum
