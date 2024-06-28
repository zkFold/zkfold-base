{-# LANGUAGE DerivingVia      #-}
{-# LANGUAGE OverloadedLists  #-}
{-# LANGUAGE TypeApplications #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module ZkFold.Base.Algebra.EllipticCurve.BLS12_381 where

import           Control.Monad
import           Data.Bits
import           Data.Foldable
import           Data.List                                  (unfoldr)
import           Data.Word
import           Numeric.Natural                            (Natural)
import           Prelude                                    hiding (Num (..), (/), (^))
import qualified Prelude                                    as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.Class
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

instance StandardEllipticCurve BLS12_381_G1 where
    aParameter = zero

    bParameter = fromConstant (4 :: Natural)

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

------------------------------------ Encoding ------------------------------------

-- infinite list of divMod 256's, little endian order
leBytesOf :: Natural -> [(Natural, Word8)]
leBytesOf n =
    let
        (n', r) = n `Prelude.divMod` 256
    in
        (n', fromIntegral r) : leBytesOf n'

-- finite list of bytes, big endian order
bytesOf :: ToConstant a Natural => Int -> a -> [Word8]
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
    put Inf         = putWord8 (bit 1) <> foldMap putWord8 (replicate 95 0)
    put (Point x y) = foldMap putWord8 (bytesOf 48 x <> bytesOf 48 y)
    get = do
        byte <- getWord8
        let compressed = testBit byte 0
            infinite = testBit byte 1
        if infinite then do
            skip (if compressed then 47 else 95)
            return Inf
        else do
            let byteXhead = clearBit (clearBit (clearBit byte 0) 1) 2
            bytesXtail <- replicateM 47 getWord8
            let x = ofBytes (byteXhead:bytesXtail)
                bigY = testBit byte 2
            if compressed then return (decompress (PointCompressed x bigY))
            else do
                bytesY <- replicateM 48 getWord8
                let y = ofBytes bytesY
                return (Point x y)

instance Binary (PointCompressed BLS12_381_G1) where
    put InfCompressed =
        putWord8 (bit 0 .|. bit 1) <> foldMap putWord8 (replicate 47 0)
    put (PointCompressed x bigY) =
        let
            flags = if bigY then bit 0 .|. bit 2 else bit 0
            bytes = bytesOf 48 x
        in
            putWord8 (flags .|. head bytes) <> foldMap putWord8 (tail bytes)
    get = do
        byte <- getWord8
        let compressed = testBit byte 0
            infinite = testBit byte 1
        if infinite then do
            skip (if compressed then 47 else 95)
            return InfCompressed
        else do
            let byteXhead = clearBit (clearBit (clearBit byte 0) 1) 2
            bytesXtail <- replicateM 47 getWord8
            let x = ofBytes (byteXhead:bytesXtail)
                bigY = testBit byte 2
            if compressed then return (PointCompressed x bigY)
            else do
                bytesY <- replicateM 48 getWord8
                let y :: Fq = ofBytes bytesY
                    bigY' = y > negate y
                return (PointCompressed x bigY')

instance Binary (Point BLS12_381_G2) where
    put Inf = putWord8 (bit 1) <> foldMap putWord8 (replicate 191  0)
    put (Point (Ext2 x0 x1) (Ext2 y0 y1)) =
        let
            bytes = bytesOf 48 x1
              <> bytesOf 48 x0
              <> bytesOf 48 y1
              <> bytesOf 48 y0
        in
            foldMap putWord8 bytes
    get = do
        byte <- getWord8
        let compressed = testBit byte 0
            infinite = testBit byte 1
        if infinite then do
            skip (if compressed then 95 else 191)
            return Inf
        else do
            let byteX1head = clearBit (clearBit (clearBit byte 0) 1) 2
            bytesX1tail <- replicateM 47 getWord8
            bytesX0 <- replicateM 48 getWord8
            let x1 = ofBytes (byteX1head:bytesX1tail)
                x0 = ofBytes bytesX0
                bigY = testBit byte 2
            if compressed then return (decompress (PointCompressed (Ext2 x0 x1) bigY))
            else do
                bytesY1 <- replicateM 48 getWord8
                bytesY0 <- replicateM 48 getWord8
                let y0 = ofBytes bytesY0
                    y1 = ofBytes bytesY1
                return (Point (Ext2 x0 x1) (Ext2 y0 y1))

instance Binary (PointCompressed BLS12_381_G2) where
    put InfCompressed =
        putWord8 (bit 0 .|. bit 1) <> foldMap putWord8 (replicate 95 0)
    put (PointCompressed (Ext2 x0 x1) bigY) =
        let
            flags = if bigY then bit 0 .|. bit 2 else bit 0
            bytes = bytesOf 48 x1 <> bytesOf 48 x0
        in
            putWord8 (flags .|. head bytes) <> foldMap putWord8 (tail bytes)
    get = do
        byte <- getWord8
        let compressed = testBit byte 0
            infinite = testBit byte 1
        if infinite then do
            skip (if compressed then 95 else 191)
            return InfCompressed
        else do
            let byteX1head = clearBit (clearBit (clearBit byte 0) 1) 2
            bytesX1tail <- replicateM 47 getWord8
            bytesX0 <- replicateM 48 getWord8
            let x1 = ofBytes (byteX1head:bytesX1tail)
                x0 = ofBytes bytesX0
                x = Ext2 x0 x1
                bigY = testBit byte 2
            if compressed then return (PointCompressed (Ext2 x0 x1) bigY)
            else do
                bytesY1 <- replicateM 48 getWord8
                bytesY0 <- replicateM 48 getWord8
                let y0 = ofBytes bytesY0
                    y1 = ofBytes bytesY1
                    y :: Fq2 = Ext2 y0 y1
                    bigY' = y > negate y
                return (PointCompressed x bigY')

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

instance Pairing BLS12_381_G1 BLS12_381_G2 BLS12_381_GT where
    pairing a b = BLS12_381_GT (pairingBLS a b)

-- Adapted from https://github.com/nccgroup/pairing-bls12381/blob/master/Crypto/Pairing_bls12381.hs

-- Untwist point on E2 for pairing calculation
untwist :: Point BLS12_381_G2 -> (Fq12, Fq12)
untwist (Point x1 y1) = (wideX, wideY)
  where
    root = Ext3 zero one zero
    wideX = Ext2 zero (Ext3 zero zero x1) // Ext2 zero root
    wideY = Ext2 zero (Ext3 zero zero y1) // Ext2 root zero
untwist Inf = error "untwist: point at infinity"

-- Used in miller loop for computing line functions l_r,r and v_2r
doubleEval :: Point BLS12_381_G2 -> Point BLS12_381_G1 -> Fq12
doubleEval r (Point px py) = fromConstant py - (fromConstant px * slope) - v
  where
    (rx, ry) = untwist r
    slope = (rx * rx + rx * rx + rx * rx) // (ry + ry)
    v = ry - slope * rx
doubleEval _ Inf = error "doubleEval: point at infinity"

-- Used in miller loop for computer line function l_r,p and v_r+p
addEval :: Point BLS12_381_G2 -> Point BLS12_381_G2 -> Point BLS12_381_G1 -> Fq12
addEval r q p@(Point px _) = if (rx == qx) && (ry + qy == zero)
                then fromConstant px - rx
                else addEval' (rx, ry) (qx, qy) p
  where
    (rx, ry) = untwist r
    (qx, qy) = untwist q
addEval _ _ Inf = error "addEval: point at infinity"

-- Helper function for addEval
addEval' :: (Fq12, Fq12) -> (Fq12, Fq12) -> Point BLS12_381_G1 -> Fq12
addEval' (rx, ry) (qx, qy) (Point px py) = fromConstant py - (fromConstant px * slope) - v
  where
    slope = (qy - ry) // (qx - rx)
    v = ((qy * rx) - (ry * qx)) // (rx - qx)
addEval' _ _ Inf = error "addEval': point at infinity"

-- Classic Miller loop for Ate pairing
miller :: Point BLS12_381_G1 -> Point BLS12_381_G2 -> Fq12
miller p q = miller' p q q iterations one
  where
    iterations = tail $ reverse $  -- list of true/false per bits of operand
      unfoldr (\b -> if b == (0 :: Integer) then Nothing
                     else Just(odd b, shiftR b 1)) 0xd201000000010000

-- Double and add loop helper for Miller (iterative)
miller' :: Point BLS12_381_G1 -> Point BLS12_381_G2 -> Point BLS12_381_G2 -> [Bool] -> Fq12 -> Fq12
miller' _ _ _ [] result = result
miller' p q r (i:iters) result =
  if i then miller' p q (pointAdd doubleR q) iters (accum * addEval doubleR q p)
       else miller' p q doubleR iters accum
  where
    accum = result * result * doubleEval r p
    doubleR = pointDouble r

-- | Pairing calculation for a valid point in G1 and another valid point in G2.
pairingBLS :: Point BLS12_381_G1 -> Point BLS12_381_G2 -> Fq12
pairingBLS Inf _ = zero
pairingBLS _ Inf = zero
pairingBLS p q   = pow' (miller p q) (((order @(BaseField BLS12_381_G1))^(12 :: Natural) -! 1) `Haskell.div` (order @(ScalarField BLS12_381_G1))) one

-- Used for the final exponentiation; opportunity for further perf optimization
pow' :: MultiplicativeSemigroup a => a -> Natural -> a -> a
pow' a0 e result
  | e <= 1    = a0
  | even e    = accum2
  | otherwise = accum2 * a0
  where
    accum  = pow' a0 (shiftR e 1) result
    accum2 = accum * accum

