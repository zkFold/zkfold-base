{-# LANGUAGE DerivingVia #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Algebra.EllipticCurve.Pasta where

import           Prelude

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Data.ByteString

-------------------------------- Introducing Fields ----------------------------------

type FpModulus = 0x40000000000000000000000000000000224698fc094cf91b992d30ed00000001
instance Prime FpModulus

type FqModulus = 0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001
instance Prime FqModulus

type Fp = Zp FpModulus
type Fq = Zp FqModulus

------------------------------------ Pallas ------------------------------------

data Pallas

instance EllipticCurve Pallas where
    type ScalarField Pallas = Fq

    type BaseField Pallas = Fp

    inf = Inf

    gen = Point
        0x40000000000000000000000000000000224698fc094cf91b992d30ed00000000
        0x02

    add = addPoints

    mul = pointMul

instance StandardEllipticCurve Pallas where
    aParameter = zero

    bParameter = fromConstant (5 :: Natural)

------------------------------------ Vesta ------------------------------------

data Vesta

instance EllipticCurve Vesta where

    type ScalarField Vesta = Fp

    type BaseField Vesta = Fq

    inf = Inf

    gen = Point
        0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000000
        0x02

    add = addPoints

    mul = pointMul

instance StandardEllipticCurve Vesta where
    aParameter = zero

    bParameter = fromConstant (5 :: Natural)

------------------------------------ Encoding ------------------------------------

instance Binary (Point Pallas) where
  put Inf           = put (Point @Pallas zero zero)
  put (Point xp yp) = put xp >> put yp
  get = do
    xp <- get
    yp <- get
    return $
      if xp == zero && yp == zero
      then Inf
      else Point xp yp

instance Binary (Point Vesta) where
  put Inf           = put (Point @Vesta zero zero)
  put (Point xp yp) = put xp >> put yp
  get = do
    xp <- get
    yp <- get
    return $
      if xp == zero && yp == zero
      then Inf
      else Point xp yp
