{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE OverloadedLists      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Algebra.EllipticCurve.BLS12_381 where

import           Control.DeepSeq                            (NFData)
import           Control.Monad
import           Data.Bits
import           Data.Foldable
import           Data.Word
import           GHC.Generics                               (Generic)
import           Prelude                                    hiding (Num (..), (/), (^))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
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
    deriving (Generic, NFData)

instance EllipticCurve BLS12_381_G1 where
    type ScalarField BLS12_381_G1 = Fr

    type BaseField BLS12_381_G1 = Fq

    gen = point
        0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb
        0x8b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1

    add = addPoints

    mul = pointMul

instance StandardEllipticCurve BLS12_381_G1 where
    aParameter = zero

    bParameter = fromConstant (4 :: Natural)

------------------------------------ BLS12-381 G2 ------------------------------------

data BLS12_381_G2
    deriving (Generic, NFData)

instance EllipticCurve BLS12_381_G2 where

    type ScalarField BLS12_381_G2 = Fr

    type BaseField BLS12_381_G2 = Fq2

    gen = point
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

------------------------------------ Encoding ------------------------------------

-- infinite list of divMod 256's, little endian order
leBytesOf :: Natural -> [(Natural, Word8)]
leBytesOf n =
    let
        (n', r) = n `Prelude.divMod` 256
    in
        (n', fromIntegral r) : leBytesOf n'

-- finite list of bytes, big endian order
bytesOf :: (ToConstant a, Const a ~ Natural) => Int -> a -> [Word8]
bytesOf n
    = reverse
    . take n
    . map snd
    . leBytesOf
    . toConstant

-- big endian decoding
ofBytes :: FromConstant Natural a => [Word8] -> a
ofBytes
  = fromConstant @Natural
  . foldl' (\n w8 -> n * 256 + fromIntegral w8) 0

instance Binary (Point BLS12_381_G1) where
    put (Point x y isInf) =
        if isInf then foldMap putWord8 (bitReverse8 (bit 1) : replicate 95 0)
                 else foldMap putWord8 (bytesOf 48 x <> bytesOf 48 y)
    get = do
        byte <- bitReverse8 <$> getWord8
        let compressed = testBit byte 0
            infinite = testBit byte 1
        if infinite then do
            skip (if compressed then 47 else 95)
            return inf
        else do
            let byteXhead = bitReverse8 $ clearBit (clearBit (clearBit byte 0) 1) 2
            bytesXtail <- replicateM 47 getWord8
            let x = ofBytes (byteXhead:bytesXtail)
                bigY = testBit byte 2
            if compressed then return (decompress (pointCompressed x bigY))
            else do
                bytesY <- replicateM 48 getWord8
                let y = ofBytes bytesY
                return (point x y)

instance Binary (PointCompressed BLS12_381_G1) where
    put (PointCompressed x bigY isInf) =
        if isInf then foldMap putWord8 (bitReverse8 (bit 0 .|. bit 1) : replicate 47 0)
        else
        let
            flags = bitReverse8 $ if bigY then bit 0 .|. bit 2 else bit 0
            bytes = bytesOf 48 x
        in foldMap putWord8 ((flags .|. head bytes) : tail bytes)
    get = do
        byte <- bitReverse8 <$> getWord8
        let compressed = testBit byte 0
            infinite = testBit byte 1
        if infinite then do
            skip (if compressed then 47 else 95)
            return inf
        else do
            let byteXhead = bitReverse8 $ clearBit (clearBit (clearBit byte 0) 1) 2
            bytesXtail <- replicateM 47 getWord8
            let x = ofBytes (byteXhead:bytesXtail)
                bigY = testBit byte 2
            if compressed then return (pointCompressed x bigY)
            else do
                bytesY <- replicateM 48 getWord8
                let y :: Fq = ofBytes bytesY
                    bigY' = y > negate y
                return (pointCompressed x bigY')

instance Binary (Point BLS12_381_G2) where
    put (Point (Ext2 x0 x1) (Ext2 y0 y1) isInf) =
        if isInf then foldMap putWord8 (bitReverse8 (bit 1) : replicate 191  0)
        else
        let
            bytes = bytesOf 48 x1
              <> bytesOf 48 x0
              <> bytesOf 48 y1
              <> bytesOf 48 y0
        in
            foldMap putWord8 bytes
    get = do
        byte <- bitReverse8 <$> getWord8
        let compressed = testBit byte 0
            infinite = testBit byte 1
        if infinite then do
            skip (if compressed then 95 else 191)
            return inf
        else do
            let byteX1head = bitReverse8 $ clearBit (clearBit (clearBit byte 0) 1) 2
            bytesX1tail <- replicateM 47 getWord8
            bytesX0 <- replicateM 48 getWord8
            let x1 = ofBytes (byteX1head:bytesX1tail)
                x0 = ofBytes bytesX0
                bigY = testBit byte 2
            if compressed then return (decompress (pointCompressed (Ext2 x0 x1) bigY))
            else do
                bytesY1 <- replicateM 48 getWord8
                bytesY0 <- replicateM 48 getWord8
                let y0 = ofBytes bytesY0
                    y1 = ofBytes bytesY1
                return (point (Ext2 x0 x1) (Ext2 y0 y1))

instance Binary (PointCompressed BLS12_381_G2) where
    put (PointCompressed (Ext2 x0 x1) bigY isInf) =
        if isInf then foldMap putWord8 (bitReverse8 (bit 0 .|. bit 1) : replicate 95 0)
        else
        let
            flags = bitReverse8 $ if bigY then bit 0 .|. bit 2 else bit 0
            bytes = bytesOf 48 x1 <> bytesOf 48 x0
        in
            foldMap putWord8 ((flags .|. head bytes) : tail bytes)
    get = do
        byte <- bitReverse8 <$> getWord8
        let compressed = testBit byte 0
            infinite = testBit byte 1
        if infinite then do
            skip (if compressed then 95 else 191)
            return inf
        else do
            let byteX1head = bitReverse8 $ clearBit (clearBit (clearBit byte 0) 1) 2
            bytesX1tail <- replicateM 47 getWord8
            bytesX0 <- replicateM 48 getWord8
            let x1 = ofBytes (byteX1head:bytesX1tail)
                x0 = ofBytes bytesX0
                x = Ext2 x0 x1
                bigY = testBit byte 2
            if compressed then return (pointCompressed (Ext2 x0 x1) bigY)
            else do
                bytesY1 <- replicateM 48 getWord8
                bytesY0 <- replicateM 48 getWord8
                let y0 = ofBytes bytesY0
                    y1 = ofBytes bytesY1
                    y :: Fq2 = Ext2 y0 y1
                    bigY' = y > negate y
                return (pointCompressed x bigY')

--------------------------------------- Pairing ---------------------------------------

-- | An image of a pairing is a cyclic multiplicative subgroup of @'Fq12'@
-- of order @'BLS12_381_Scalar'@.
newtype BLS12_381_GT = BLS12_381_GT Fq12
    deriving newtype (Eq, Show, MultiplicativeSemigroup, MultiplicativeMonoid)

instance Exponent BLS12_381_GT Natural where
    BLS12_381_GT a ^ p = BLS12_381_GT (a ^ p)

instance Exponent BLS12_381_GT Integer where
    BLS12_381_GT a ^ p = BLS12_381_GT (a ^ p)

deriving via (NonZero Fq12) instance MultiplicativeGroup BLS12_381_GT

instance Finite BLS12_381_GT where
    type Order BLS12_381_GT = BLS12_381_Scalar

instance Pairing BLS12_381_G1 BLS12_381_G2 where
    type TargetGroup BLS12_381_G1 BLS12_381_G2 = BLS12_381_GT
    pairing a b
      = BLS12_381_GT
      $ finalExponentiation @BLS12_381_G2
      $ millerAlgorithmBLS12 param a b
      where
        param = [-1
          ,-1, 0,-1, 0, 0,-1, 0, 0, 0, 0, 0, 0, 0, 0,-1, 0
          , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
          , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,-1, 0
          , 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
          ]
