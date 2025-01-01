{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Algebra.EllipticCurve2.Pasta
  ( Pallas_Point
  , Vesta_Point
  , FpModulus
  , FqModulus
  , Fp
  , Fq
  ) where

import Control.Monad
import Data.Type.Equality
import qualified Prelude
import Prelude (($))

import ZkFold.Base.Algebra.Basic.Class
import ZkFold.Base.Algebra.Basic.Field
import ZkFold.Base.Algebra.Basic.Number
import ZkFold.Base.Algebra.EllipticCurve2.Class
import ZkFold.Base.Data.ByteString
import ZkFold.Symbolic.Data.Bool
import ZkFold.Symbolic.Data.Conditional
import ZkFold.Symbolic.Data.Eq

-------------------------------- Introducing Fields ----------------------------------

type FpModulus = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
instance Prime FpModulus

type FqModulus = 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001
instance Prime FqModulus

type Fp = Zp FpModulus
type Fq = Zp FqModulus

------------------------------------ Pallas ------------------------------------

type Pallas_Point = Weierstrass "Pallas" (Point Prelude.Bool) Fp

instance Field field => WeierstrassCurve "Pallas" field where
  weierstrassB = fromConstant (5 :: Natural)

instance
  ( Conditional bool bool
  , Conditional bool baseField
  , Eq bool baseField
  , FiniteField baseField
  , Order baseField ~ FpModulus
  , scalarField ~ Fq
  ) => SubgroupCurve "Pallas" bool baseField scalarField (Weierstrass "Pallas" (Point bool)) where
    pointGen = pointXY
      (fromConstant (0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000 :: Natural))
      (fromConstant (0x02 :: Natural))

instance
  ( Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Field field
  ) => Scale Fq (Weierstrass "Pallas" (Point bool) field) where
    scale n x = scale (toConstant n) x

------------------------------------ Vesta ------------------------------------

type Vesta_Point = Weierstrass "Vesta" (Point Prelude.Bool) Fq

instance Field field => WeierstrassCurve "Vesta" field where
  weierstrassB = fromConstant (5 :: Natural)

instance
  ( Conditional bool bool
  , Conditional bool baseField
  , Eq bool baseField
  , FiniteField baseField
  , Order baseField ~ FqModulus
  , scalarField ~ Fp
  ) => SubgroupCurve "Vesta" bool baseField scalarField (Weierstrass "Vesta" (Point bool)) where
    pointGen = pointXY
      (fromConstant (0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000000 :: Natural))
      (fromConstant (0x02 :: Natural))

instance
  ( Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Field field
  ) => Scale Fp (Weierstrass "Vesta" (Point bool) field) where
    scale n x = scale (toConstant n) x

------------------------------------ Encoding ------------------------------------

instance Binary Pallas_Point where
  put (Weierstrass (Point xp yp isInf)) =
    if isInf then put @Pallas_Point (pointXY zero zero) else put xp >> put yp
  get = do
    xp <- get
    yp <- get
    return $
      if xp == zero && yp == zero
      then pointInf
      else pointXY xp yp

instance Binary Vesta_Point where
  put (Weierstrass (Point xp yp isInf)) =
    if isInf then put @Vesta_Point (pointXY zero zero) else put xp >> put yp
  get = do
    xp <- get
    yp <- get
    return $
      if xp == zero && yp == zero
      then pointInf
      else pointXY xp yp
