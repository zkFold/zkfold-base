{-# LANGUAGE DerivingVia     #-}
{-# LANGUAGE OverloadedLists #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Algebra.EllipticCurve.BN254
  ( BN254_Scalar
  , BN254_Base
  , Fr
  , Fp
  , Fp2
  , Fp6
  , Fp12
  , BN254_G1
  , BN254_G2
  , BN254_GT) where

import           Control.Monad                              (return, (>>))
import           Data.Binary                                (Binary (..))
import           Data.Bool                                  ((&&))
import           Data.Eq                                    (Eq (..))
import           Data.Function                              (($))
import           Prelude                                    (Integer)
import           Text.Show                                  (Show)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field            (Ext2 (..), Ext3 (..), IrreduciblePoly (..), Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.EllipticCurve.Pairing
import           ZkFold.Base.Algebra.Polynomials.Univariate (toPoly)

-------------------------- Scalar field & field towers -------------------------

-- Designations of curve parameters are as in:
-- https://pkg.go.dev/github.com/consensys/gnark-crypto/ecc/bn254

type BN254_Scalar = 21888242871839275222246405745257275088548364400416034343698204186575808495617
instance Prime BN254_Scalar

type BN254_Base = 21888242871839275222246405745257275088696311157297823662689037894645226208583
instance Prime BN254_Base

type Fr = Zp BN254_Scalar
type Fp = Zp BN254_Base

instance IrreduciblePoly Fp "IP1" where
  irreduciblePoly = toPoly [1, 0, 1]

type Fp2 = Ext2 Fp "IP1"

-- cubic nonresidue in @Fp2@.
xi :: Fp2
xi = Ext2 9 1

instance IrreduciblePoly Fp2 "IP2" where
  irreduciblePoly = toPoly [negate xi, zero, zero, one]

type Fp6 = Ext3 Fp2 "IP2"

instance IrreduciblePoly Fp6 "IP3" where
  irreduciblePoly = toPoly [Ext3 zero (negate one) zero, zero, one]

type Fp12 = Ext2 Fp6 "IP3"

------------------------------- bn254 G1 ---------------------------------------

data BN254_G1

instance EllipticCurve BN254_G1 where
  type ScalarField BN254_G1 = Fr
  type BaseField BN254_G1 = Fp
  gen = point 1 2
  add = addPoints
  mul = pointMul

instance StandardEllipticCurve BN254_G1 where
  aParameter = 0
  bParameter = 3

------------------------------- bn254 G2 ---------------------------------------

data BN254_G2

instance EllipticCurve BN254_G2 where
  type ScalarField BN254_G2 = Fr
  type BaseField BN254_G2 = Fp2
  gen = point
    (Ext2 0x1800deef121f1e76426a00665e5c4479674322d4f75edadd46debd5cd992f6ed
          0x198e9393920d483a7260bfb731fb5d25f1aa493335a9e71297e485b7aef312c2)
    (Ext2 0x12c85ea5db8c6deb4aab71808dcb408fe3d1e7690c43d37b4ce6cc0166fa7daa
          0x90689d0585ff075ec9e99ad690c3395bc4b313370b38ef355acdadcd122975b)
  add = addPoints
  mul = pointMul

instance StandardEllipticCurve BN254_G2 where
  aParameter = zero
  bParameter =
    Ext2 0x2b149d40ceb8aaae81be18991be06ac3b5b4c5e559dbefa33267e6dc24a138e5
         0x9713b03af0fed4cd2cafadeed8fdf4a74fa084e52d1852e4a2bd0685c315d2

------------------------------- Pairing ----------------------------------------

newtype BN254_GT = BN254_GT Fp12
  deriving (Eq, Show, MultiplicativeSemigroup, MultiplicativeMonoid)

instance Exponent BN254_GT Natural where
  BN254_GT e ^ p = BN254_GT (e ^ p)

instance Exponent BN254_GT Integer where
  BN254_GT e ^ p = BN254_GT (e ^ p)

deriving via (NonZero Fp12) instance MultiplicativeGroup BN254_GT

instance Finite BN254_GT where
  type Order BN254_GT = BN254_Scalar

instance Pairing BN254_G1 BN254_G2 where
  type TargetGroup BN254_G1 BN254_G2 = BN254_GT
  pairing p q
    = BN254_GT
    $ finalExponentiation @BN254_G2
    $ millerAlgorithmBN xi param p q
    where
      param = [ 1
        , 1, 0, 1, 0, 0,-1, 0, 1, 1, 0, 0, 0,-1, 0, 0, 1
        , 1, 0, 0,-1, 0, 0, 0, 0, 0, 1, 0, 0,-1, 0, 0, 1
        , 1, 1, 0, 0, 0, 0,-1, 0, 1, 0, 0,-1, 0, 1, 1, 0
        , 0, 1, 0, 0,-1, 1, 0, 0,-1, 0, 1, 0, 1, 0, 0, 0
        ]

------------------------------ Encoding ----------------------------------------

instance Binary (Point BN254_G1) where
  put (Point xp yp isInf) =
    if isInf then put @(Point BN254_G1) (point zero zero) else put xp >> put yp
  get = do
    xp <- get
    yp <- get
    return $
      if xp == zero && yp == zero
      then inf
      else point xp yp

instance Binary (Point BN254_G2) where
  put (Point xp yp isInf) =
    if isInf then put @(Point BN254_G2) (point zero zero) else put xp >> put yp
  get = do
    xp <- get
    yp <- get
    return $
      if xp == zero && yp == zero
      then inf
      else point xp yp
