{-# LANGUAGE DerivingVia     #-}
{-# LANGUAGE OverloadedLists #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Algebra.EllipticCurve.BLS12_381 where

import           Prelude                                    hiding (Num (..), (/), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Algebra.EllipticCurve.Encoding
import           ZkFold.Base.Algebra.EllipticCurve.Pairing
import           ZkFold.Base.Algebra.Polynomials.Univariate
import           ZkFold.Base.Data.ByteString

-------------------------------- Introducing Fields ----------------------------------

type BLS12_381_Scalar = 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
instance Prime BLS12_381_Scalar

type BLS12_381_Base = 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
instance Prime BLS12_381_Base

type Fr = Zp BLS12_381_Scalar
type Fq = Zp BLS12_381_Base

type IP1 = "IP1"
instance IrreduciblePoly Fq IP1 where
    irreduciblePoly = toPoly [1, 0, 1]
type Fq2 = Ext2 Fq IP1

type IP2 = "IP2"
instance IrreduciblePoly Fq2 IP2 where
    irreduciblePoly =
        let e = Ext2
                0xd0088f51cbff34d258dd3db21a5d66bb23ba5c279c2895fb39869507b587b120f55ffff58a9ffffdcff7fffffffd556
                0xd0088f51cbff34d258dd3db21a5d66bb23ba5c279c2895fb39869507b587b120f55ffff58a9ffffdcff7fffffffd555
        in toPoly [negate e, zero, zero, one]
type Fq6 = Ext3 Fq2 IP2

type IP3 = "IP3"
instance IrreduciblePoly Fq6 IP3 where
    irreduciblePoly =
        let e = Ext3 zero (negate one) zero
        in toPoly [e, zero, one]
type Fq12 = Ext2 Fq6 IP3

------------------------------------ BLS12-381 G1 ------------------------------------

data BLS12_381_G1

instance EllipticCurve BLS12_381_G1 where
    type ScalarField BLS12_381_G1 = Fr

    type BaseField BLS12_381_G1 = Fq

    inf = Inf

    gen = Point
        0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb
        0x8b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1

    add = addPoints

    mul = pointMul

instance StandardEllipticCurve BLS12_381_G1 where
    aParameter = zero

    bParameter = fromConstant (4 :: Natural)

------------------------------------ BLS12-381 G2 ------------------------------------

data BLS12_381_G2

instance EllipticCurve BLS12_381_G2 where

    type ScalarField BLS12_381_G2 = Fr

    type BaseField BLS12_381_G2 = Fq2

    inf = Inf

    gen = Point
        (Ext2
            0x24aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8
            0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e)
        (Ext2
            0xce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801
            0x606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be)

    add = addPoints

    mul = pointMul

instance StandardEllipticCurve BLS12_381_G2 where
    aParameter = zero

    bParameter = fromConstant (4 :: Natural)

--------------------------------------- Pairing ---------------------------------------

-- | An image of a pairing is a cyclic multiplicative subgroup of @'Fq12'@
-- of order @'BLS12_381_Scalar'@.
newtype BLS12_381_GT = BLS12_381_GT Fq12
    deriving newtype (Eq, MultiplicativeSemigroup, MultiplicativeMonoid)

instance Exponent BLS12_381_GT Natural where
    BLS12_381_GT a ^ p = BLS12_381_GT (a ^ p)

instance Exponent BLS12_381_GT Integer where
    BLS12_381_GT a ^ p = BLS12_381_GT (a ^ p)

deriving via (NonZero Fq12) instance MultiplicativeGroup BLS12_381_GT

instance Finite BLS12_381_GT where
    type Order BLS12_381_GT = BLS12_381_Scalar

instance Pairing BLS12_381_G1 BLS12_381_G2 where
    type TargetGroup BLS12_381_G1 BLS12_381_G2 = BLS12_381_GT
    pairing a b = BLS12_381_GT (ate a b)

-------------------------------------- Encoding ---------------------------------------

instance Binary (Point BLS12_381_G1) where
    put = putPointZp
    get = getPointZp

instance Binary (PointCompressed BLS12_381_G1) where
    put = putCompressedPointZp
    get = getCompressedPointZp

instance Binary (Point BLS12_381_G2) where
    put = putPointExt2
    get = getPointExt2

instance Binary (PointCompressed BLS12_381_G2) where
    put = putCompressedPointExt2
    get = getCompressedPointExt2
