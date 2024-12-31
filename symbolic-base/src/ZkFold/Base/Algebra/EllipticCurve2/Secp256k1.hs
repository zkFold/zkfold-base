{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Algebra.EllipticCurve2.Secp256k1
  ( Secp256k1_Point
  , Secp256k1_Base
  , Secp256k1_Scalar
  , Fn
  , Fp
  , Secp256k1 (..)
  ) where

import Data.Type.Equality
import qualified Prelude

import ZkFold.Base.Algebra.Basic.Class
import ZkFold.Base.Algebra.Basic.Field
import ZkFold.Base.Algebra.Basic.Number
import ZkFold.Base.Algebra.EllipticCurve2.Class
import ZkFold.Symbolic.Data.Bool
import ZkFold.Symbolic.Data.Conditional
import ZkFold.Symbolic.Data.Eq

type Secp256k1_Point = Secp256k1 Prelude.Bool Fp

type Secp256k1_Scalar = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
instance Prime Secp256k1_Scalar

type Secp256k1_Base = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
instance Prime Secp256k1_Base

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
  ) => SubgroupCurve "secp256k1" bool baseField scalarField (Secp256k1 bool) where
    pointGen = pointXY
      (fromConstant (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798 :: Natural))
      (fromConstant (0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8 :: Natural))

newtype Secp256k1 bool field = Secp256k1
  {curveSecp256k1 :: Weierstrass "secp256k1" (Point bool) field}
deriving newtype instance
  ( Conditional bool bool
  , Conditional bool field
  ) => Conditional bool (Secp256k1 bool field)
deriving newtype instance
  ( Conditional bool bool
  , Eq bool bool
  , Eq bool field
  , Field field
  ) => Eq bool (Secp256k1 bool field)
deriving newtype instance BoolType bool => Planar (Secp256k1 bool)
deriving newtype instance (BoolType bool, Semiring field)
  => HasPointInf (Secp256k1 bool field)
deriving newtype instance BoolType bool
  => FromConstant (AffinePoint field) (Secp256k1 bool field)
deriving newtype instance BoolType bool
  => FromConstant (Slope field) (Secp256k1 bool field)
deriving newtype instance
  ( Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Eq bool bool
  , Field field
  ) => ProjectivePlanar bool field (Secp256k1 bool)
deriving newtype instance
  ( Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Field field
  ) => AdditiveSemigroup (Secp256k1 bool field)
deriving newtype instance
  ( Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Field field
  ) => AdditiveMonoid (Secp256k1 bool field)
deriving newtype instance
  ( Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Field field
  ) => AdditiveGroup (Secp256k1 bool field)
deriving newtype instance
  ( Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Field field
  ) => Scale Natural (Secp256k1 bool field)
instance
  ( Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Field field
  ) => Scale Fn (Secp256k1 bool field) where
    scale n x = scale (toConstant n) x
deriving newtype instance
  ( Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Field field
  ) => Scale Prelude.Integer (Secp256k1 bool field)
deriving newtype instance
  ( Conditional bool bool
  , Conditional bool field
  , Eq bool field
  , Field field
  ) => EllipticCurve "secp256k1" bool field (Secp256k1 bool)
