{-# LANGUAGE DerivingVia     #-}
{-# LANGUAGE OverloadedLists #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Algebra.EllipticCurve.Bn254 where

import           Data.Eq                                    (Eq)
import           Prelude                                    (Integer)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field            (Ext2 (..), Ext3, IrreduciblePoly (..), Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.EllipticCurve.Pairing  (ate)
import           ZkFold.Base.Algebra.Polynomials.Univariate (Poly, toPoly)

-------------------------- Scalar field & field towers -------------------------

type Bn254_Scalar = 21888242871839275222246405745257275088548364400416034343698204186575808495617
instance Prime Bn254_Scalar

type Bn254_Base = 21888242871839275222246405745257275088696311157297823662689037894645226208583
instance Prime Bn254_Base

type Fr = Zp Bn254_Scalar
type Fp = Zp Bn254_Base

x :: (Ring a, Eq a) => Poly a
x = toPoly [zero, one]

u :: Poly Fp
u = x

instance IrreduciblePoly Fp "IP1" where
  irreduciblePoly = u ^ (2 :: Natural) + one

type Fp2 = Ext2 Fp "IP1"

v :: Poly Fp2
v = x

instance IrreduciblePoly Fp2 "IP2" where
  irreduciblePoly = v ^ (3 :: Natural) - fromConstant (9 :: Natural) - fromConstant u

type Fp6 = Ext3 Fp2 "IP2"

w :: Poly Fp6
w = x

instance IrreduciblePoly Fp6 "IP3" where
  irreduciblePoly = w ^ (2 :: Natural) - fromConstant v

type Fp12 = Ext2 Fp6 "IP3"

------------------------------- bn254 G1 ---------------------------------------

data Bn254_G1

instance EllipticCurve Bn254_G1 where
  type ScalarField Bn254_G1 = Fr
  type BaseField Bn254_G1 = Fp
  inf = Inf
  gen = Point 1 2
  add = pointAdd
  mul = pointMul

instance StandardEllipticCurve Bn254_G1 where
  aParameter = 0
  bParameter = 3

------------------------------- bn254 G2 ---------------------------------------

data Bn254_G2

instance EllipticCurve Bn254_G2 where
  type ScalarField Bn254_G2 = Fr
  type BaseField Bn254_G2 = Fp2
  inf = Inf
  gen = Point
    (Ext2 10857046999023057135944570762232829481370756359578518086990519993285655852781
          11559732032986387107991004021392285783925812861821192530917403151452391805634)
    (Ext2 8495653923123431417604973247489272438418190587263600148770280649306958101930
          4082367875863433681332203403145435568316851327593401208105741076214120093531)
  add = pointAdd
  mul = pointMul

instance StandardEllipticCurve Bn254_G2 where
  aParameter = zero
  bParameter = Ext2 3 0 // Ext2 9 1

------------------------------- Pairing ----------------------------------------

newtype Bn254_GT = Bn254_GT Fp12
  deriving (Eq, MultiplicativeSemigroup, MultiplicativeMonoid)

instance Exponent Bn254_GT Natural where
  Bn254_GT e ^ p = Bn254_GT (e ^ p)

instance Exponent Bn254_GT Integer where
  Bn254_GT e ^ p = Bn254_GT (e ^ p)

deriving via (NonZero Fp12) instance MultiplicativeGroup Bn254_GT

instance Finite Bn254_GT where
  type Order Bn254_GT = Bn254_Scalar

instance Pairing Bn254_G1 Bn254_G2 where
  type TargetGroup Bn254_G1 Bn254_G2 = Bn254_GT
  pairing p q = Bn254_GT (ate p q)
