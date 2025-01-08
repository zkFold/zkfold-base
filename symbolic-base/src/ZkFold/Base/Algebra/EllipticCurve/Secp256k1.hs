{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Algebra.EllipticCurve.Secp256k1
  ( Secp256k1_Base
  , Secp256k1_Scalar
  , Secp256k1_Point
  , Fn
  , Fp
  ) where

import           Data.Type.Equality
import qualified Prelude

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Symbolic.Data.Conditional
import           ZkFold.Symbolic.Data.Eq

type Secp256k1_Scalar = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
instance Prime Secp256k1_Scalar

type Secp256k1_Base = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
instance Prime Secp256k1_Base

type Secp256k1_Point = Weierstrass "secp256k1" (Point Prelude.Bool) Fp

type Fn = Zp Secp256k1_Scalar
type Fp = Zp Secp256k1_Base

instance Field field => WeierstrassCurve "secp256k1" field where
  weierstrassB = fromConstant (7 :: Natural)

instance
  ( Conditional bool bool
  , Conditional bool baseField
  , Eq bool baseField
  , FiniteField baseField
  , Order baseField ~ Secp256k1_Base
  , scalarField ~ Fn
  ) => SubgroupCurve "secp256k1" bool baseField scalarField (Weierstrass "secp256k1" (Point bool)) where
    pointGen = pointXY
      (fromConstant (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798 :: Natural))
      (fromConstant (0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8 :: Natural))

instance
  ( Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Field field
  ) => Scale Fn (Weierstrass "secp256k1" (Point bool) field) where
    scale n x = scale (toConstant n) x
