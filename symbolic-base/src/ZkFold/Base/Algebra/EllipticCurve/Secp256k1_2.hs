{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Algebra.EllipticCurve.Secp256k1_2
  ( Secp256k1_Point
  , Secp256k1_Base
  , Secp256k1_Scalar
  , Fn
  , Fp
  , Secp256k1 (..)
  ) where

import qualified Prelude

import ZkFold.Base.Algebra.Basic.Class
import ZkFold.Base.Algebra.Basic.Field
import ZkFold.Base.Algebra.Basic.Number
import ZkFold.Base.Algebra.EllipticCurve.Class2
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

newtype Secp256k1 bool field = Secp256k1
  {pointSecp256k1 :: Weierstrass "secp256k1" (Point bool) field}
deriving newtype instance BoolType bool => Planar (Secp256k1 bool)
deriving newtype instance (BoolType bool, Semiring field)
  => HasPointInf (Secp256k1 bool field)
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
