{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Algebra.EllipticCurve.Pairing
  ( millerAlgorithmBN
  , millerAlgorithmBLS12
  , finalExponentiation
  ) where

import qualified Data.Bool                               as H
import           Data.Function                           (($), (.))
import           Data.Functor                            ((<$>))
import           Data.Int                                (Int8)
import           Data.Tuple                              (snd)
import           Data.Type.Equality                      (type (~))
import           Numeric.Natural                         (Natural)
import           Prelude                                 (fromInteger)
import qualified Prelude

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Symbolic.Data.Bool               hiding (Bool)
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq

-- Ate pairing implementation adapted from:
-- https://github.com/sdiehl/pairing/blob/master/src/Data/Pairing/Ate.hs

type Untwisted c i j = Ext2 (Ext3 (BaseField c) i) j

finalExponentiation ::
  forall c g i j.
  (Finite (ScalarField c), Finite (BaseField c)) =>
  (g ~ Untwisted c i j, Exponent g Natural) =>
  g -> g
finalExponentiation x = x ^ ((p ^ (12 :: Natural) -! 1) `div` r)
  where
    p = order @(BaseField c)
    r = order @(ScalarField c)

millerAlgorithmBLS12 ::
  Field (BaseField c) =>
  Field (BaseField d) =>
  Scale (BaseField c) (BaseField d) =>
  EllipticCurve d =>
  Untwisted d i j ~ g =>
  Field g =>
  BooleanOf c ~ BooleanOf d =>
  [Int8] -> Point c -> Point d -> g
millerAlgorithmBLS12 (x:xs) p q = snd $
  millerLoop p q xs (H.bool (negate q) q (x Prelude.> 0), one)
millerAlgorithmBLS12 _ _ _ = one

millerAlgorithmBN ::
  PrimeField (BaseField c) =>
  Field (BaseField d) =>
  Scale (BaseField c) (BaseField d) =>
  EllipticCurve d =>
  Untwisted d i j ~ g =>
  Field g =>
  BooleanOf c ~ BooleanOf d =>
  BaseField d -> [Int8] -> Point c -> Point d -> g
millerAlgorithmBN xi (x:xs) p q = finalStepBN xi p q $
  millerLoop p q xs (H.bool (negate q) q (x Prelude.> 0), one)
millerAlgorithmBN _ _ _ _ = one

--------------------------------------------------------------------------------

finalStepBN ::
  forall c d i j g.
  PrimeField (BaseField c) =>
  Field (BaseField d) =>
  Scale (BaseField c) (BaseField d) =>
  EllipticCurve d =>
  Untwisted d i j ~ g =>
  Field g =>
  BooleanOf c ~ BooleanOf d =>
  BaseField d -> Point c -> Point d -> (Point d, g) -> g
finalStepBN xi p q (t, f) = f * f' * f''
  where
    o = order @(BaseField c)
    q1 = frobTwisted o xi q
    (t', f') = lineFunction p t q1
    q2 = negate (frobTwisted o xi q1)
    (_, f'') = lineFunction p t' q2

millerLoop ::
  Field (BaseField c) =>
  Field (BaseField d) =>
  Scale (BaseField c) (BaseField d) =>
  EllipticCurve d =>
  Untwisted d i j ~ g =>
  Field g =>
  BooleanOf c ~ BooleanOf d =>
  Point c -> Point d -> [Int8] -> (Point d, g) -> (Point d, g)
millerLoop p q = impl
  where impl []     tf = tf
        impl (x:xs) tf
          | x Prelude.== 0    = impl xs tf2
          | x Prelude.== 1    = impl xs $ additionStep p q tf2
          | H.otherwise = impl xs $ additionStep p (negate q) tf2
          where tf2 = doublingStep p tf

--------------------------------------------------------------------------------

frobTwisted ::
  forall c. (EllipticCurve c, Field (BaseField c)) => Natural -> BaseField c -> Point c -> Point c
frobTwisted q xi (Point x y isInf) =
  if isInf then pointInf else pointXY ((x ^ q) * (xi ^ tx)) ((y ^ q) * (xi ^ ty))
  where
    tx = (q -! 1) `div` 3
    ty = q `div` 2

additionStep ::
  Field (BaseField c) =>
  Field (BaseField d) =>
  Scale (BaseField c) (BaseField d) =>
  EllipticCurve d =>
  Untwisted d i j ~ g =>
  Field g =>
  BooleanOf c ~ BooleanOf d =>
  Point c -> Point d -> (Point d, g) -> (Point d, g)
additionStep p q (t, f) = (* f) <$> lineFunction p q t

doublingStep ::
  Field (BaseField c) =>
  Field (BaseField d) =>
  Scale (BaseField c) (BaseField d) =>
  EllipticCurve d =>
  Untwisted d i j ~ g =>
  Field g =>
  BooleanOf c ~ BooleanOf d =>
  Point c -> (Point d, g) -> (Point d, g)
doublingStep p (t, f) = (* f) . (* f) <$> lineFunction p t t

lineFunction ::
  EllipticCurve d =>
  Field (BaseField c) =>
  Field (BaseField d) =>
  Scale (BaseField c) (BaseField d) =>
  BooleanOf c ~ BooleanOf d =>
  Untwisted d i j ~ g =>
  Point c -> Point d -> Point d -> (Point d, g)
lineFunction (Point x y isInf) (Point x1 y1 isInf1) (Point x2 y2 isInf2) =
  if isInf || isInf1 || isInf2 then (pointInf, Ext2 (Ext3 one zero zero) zero)
  else if x1 /= x2 then (pointXY x3 y3, untwist (negate y) (x `scale` l) (y1 - l * x1))
  else if y1 + y2 == zero then (pointInf, untwist x (negate x1) zero)
  else (pointXY x3' y3', untwist (negate y) (x `scale` l') (y1 - l' * x1))
  where
    l   = (y2 - y1) // (x2 - x1)
    x3  = l * l - x1 - x2
    y3  = l * (x1 - x3) - y1
    x12 = x1 * x1
    l'  = (x12 + x12 + x12) // (y1 + y1)
    x3' = l' * l' - x1 - x2
    y3' = l' * (x1 - x3') - y1
    untwist a b c = Ext2 (Ext3 (a `scale` one) zero zero) (Ext3 b c zero)
