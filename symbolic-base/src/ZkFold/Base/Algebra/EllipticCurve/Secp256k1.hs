{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Algebra.EllipticCurve.Secp256k1
  ( Secp256k1
  , Secp256k1_Base
  , Secp256k1_Scalar
  , Fp
  , Fn
  ) where

import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class

-------------------------- Scalar field ----------------------------------------

-- Designations of curve parameters are as in:
-- https://www.secg.org/sec2-v2.pdf

type Secp256k1_Scalar = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
instance Prime Secp256k1_Scalar

type Secp256k1_Base = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
instance Prime Secp256k1_Base

type Fn = Zp Secp256k1_Scalar
type Fp = Zp Secp256k1_Base

------------------------------- secp25k6k1 ---------------------------------------

data Secp256k1

instance EllipticCurve Secp256k1 where
  type ScalarField Secp256k1 = Fn
  type BaseField Secp256k1 = Fp
  pointGen = pointXY
    0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
    0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
  add = addPoints
  mul = pointMul

instance WeierstrassCurve Secp256k1 where
  weierstrassA = 0
  weierstrassB = 7
