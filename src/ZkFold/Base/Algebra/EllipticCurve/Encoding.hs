{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Algebra.EllipticCurve.Encoding
  ( putPointZp
  , getPointZp
  , putCompressedPointZp
  , getCompressedPointZp
  , putPointExt2
  , getPointExt2
  , putCompressedPointExt2
  , getCompressedPointExt2) where

import           Control.Monad                           (replicateM, return)
import           Data.Binary                             (Get, Put)
import           Data.Bits                               (bit, clearBit, testBit, (.|.))
import           Data.Foldable                           (foldMap, foldl')
import           Data.Function                           ((.))
import           Data.Int                                (Int)
import           Data.List                               (head, tail)
import           Data.Semigroup                          ((<>))
import           Data.Type.Equality                      (type (~))
import           Data.Word                               (Word8)
import           Numeric.Natural                         (Natural)
import           Prelude                                 (fromIntegral)
import qualified Prelude

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.EllipticCurve.Class
import           ZkFold.Base.Data.ByteString

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
    = Prelude.reverse
    . Prelude.take n
    . Prelude.map Prelude.snd
    . leBytesOf
    . toConstant

-- big endian decoding
ofBytes :: FromConstant Natural a => [Word8] -> a
ofBytes
  = fromConstant @Natural
  . foldl' (\n w8 -> n * 256 + fromIntegral w8) 0

wordCount :: forall a. Finite a => Int
wordCount = fromIntegral (numberOfBits @a) `Prelude.div` 8

putPointZp :: forall curve p. (BaseField curve ~ Zp p, Finite (Zp p)) => Point curve -> Put
putPointZp Inf         = foldMap putWord8 (bit 1 : Prelude.replicate (wordCount @(Zp p) Prelude.* 2 Prelude.- 1) 0)
putPointZp (Point x y) = foldMap putWord8 (bytesOf (wordCount @(Zp p)) x <> bytesOf (wordCount @(Zp p)) y)

getPointZp :: forall curve p. (StandardEllipticCurve curve, BaseField curve ~ Zp p, PrimeField (Zp p)) => Get (Point curve)
getPointZp = do
    byte <- getWord8
    let compressed = testBit byte 0
        infinite = testBit byte 1
    if infinite then do
        skip (if compressed then wordCount @(Zp p) Prelude.- 1 else wordCount @(Zp p) Prelude.* 2 Prelude.- 1)
        return Inf
    else do
        let byteXhead = clearBit (clearBit (clearBit byte 0) 1) 2
        bytesXtail <- replicateM (wordCount @(Zp p) Prelude.- 1) getWord8
        let x = ofBytes (byteXhead:bytesXtail)
            bigY = testBit byte 2
        if compressed then return (decompress (PointCompressed x bigY))
        else do
            bytesY <- replicateM (wordCount @(Zp p)) getWord8
            let y = ofBytes bytesY
            return (Point x y)

putCompressedPointZp :: forall curve p. (BaseField curve ~ Zp p, Finite (Zp p)) => PointCompressed curve -> Put
putCompressedPointZp InfCompressed            =
    foldMap putWord8 ((bit 0 .|. bit 1) : Prelude.replicate (wordCount @(Zp p) Prelude.- 1) 0)
putCompressedPointZp (PointCompressed x bigY) =
    let
        flags = if bigY then bit 0 .|. bit 2 else bit 0
        bytes = bytesOf (wordCount @(Zp p)) x
    in
        foldMap putWord8 ((flags .|. head bytes) : tail bytes)

getCompressedPointZp :: forall curve p. (BaseField curve ~ Zp p, Finite (Zp p)) => Get (PointCompressed curve)
getCompressedPointZp = do
    byte <- getWord8
    let compressed = testBit byte 0
        infinite = testBit byte 1
    if infinite then do
        skip (if compressed then wordCount @(Zp p) Prelude.- 1 else wordCount @(Zp p) Prelude.* 2 Prelude.- 1)
        return InfCompressed
    else do
        let byteXhead = clearBit (clearBit (clearBit byte 0) 1) 2
        bytesXtail <- replicateM (wordCount @(Zp p) Prelude.- 1) getWord8
        let x = ofBytes (byteXhead:bytesXtail)
            bigY = testBit byte 2
        if compressed then return (PointCompressed x bigY)
        else do
            bytesY <- replicateM (wordCount @(Zp p)) getWord8
            let y :: Zp p = ofBytes bytesY
                bigY' = y Prelude.> negate y
            return (PointCompressed x bigY')

putPointExt2 :: forall curve p i . (BaseField curve ~ Ext2 (Zp p) i, Finite (Zp p)) => Point curve -> Put
putPointExt2 Inf                               =
    foldMap putWord8 (bit 1 : Prelude.replicate (wordCount @(Zp p) Prelude.* 4 Prelude.- 1)  0)
putPointExt2 (Point (Ext2 x0 x1) (Ext2 y0 y1)) =
    let
        bytes = bytesOf (wordCount @(Zp p)) x1
          <> bytesOf (wordCount @(Zp p)) x0
          <> bytesOf (wordCount @(Zp p)) y1
          <> bytesOf (wordCount @(Zp p)) y0
    in
        foldMap putWord8 bytes

getPointExt2 :: forall curve p i . (StandardEllipticCurve curve, BaseField curve ~ Ext2 (Zp p) i, FiniteField (Ext2 (Zp p) i), PrimeField (Zp p)) => Get (Point curve)
getPointExt2 = do
    byte <- getWord8
    let compressed = testBit byte 0
        infinite = testBit byte 1
    if infinite then do
        skip (if compressed then wordCount @(Zp p) Prelude.* 2 Prelude.- 1 else wordCount @(Zp p) Prelude.* 4 Prelude.- 1)
        return Inf
    else do
        let byteX1head = clearBit (clearBit (clearBit byte 0) 1) 2
        bytesX1tail <- replicateM (wordCount @(Zp p) Prelude.- 1) getWord8
        bytesX0 <- replicateM (wordCount @(Zp p)) getWord8
        let x1 = ofBytes (byteX1head:bytesX1tail)
            x0 = ofBytes bytesX0
            bigY = testBit byte 2
        if compressed then return (decompress (PointCompressed (Ext2 x0 x1) bigY))
        else do
            bytesY1 <- replicateM (wordCount @(Zp p)) getWord8
            bytesY0 <- replicateM (wordCount @(Zp p)) getWord8
            let y0 = ofBytes bytesY0
                y1 = ofBytes bytesY1
            return (Point (Ext2 x0 x1) (Ext2 y0 y1))

putCompressedPointExt2 :: forall curve p i. (BaseField curve ~ Ext2 (Zp p) i, Finite (Zp p)) => PointCompressed curve -> Put
putCompressedPointExt2 InfCompressed = foldMap putWord8 ((bit 0 .|. bit 1) : Prelude.replicate (wordCount @(Zp p) Prelude.* 2 Prelude.- 1) 0)
putCompressedPointExt2 (PointCompressed (Ext2 x0 x1) bigY) =
    let
        flags = if bigY then bit 0 .|. bit 2 else bit 0
        bytes = bytesOf (wordCount @(Zp p)) x1 <> bytesOf (wordCount @(Zp p)) x0
    in
        foldMap putWord8 ((flags .|. head bytes) : tail bytes)

getCompressedPointExt2 :: forall curve p i. (BaseField curve ~ Ext2 (Zp p) i, PrimeField (Zp p)) => Get (PointCompressed curve)
getCompressedPointExt2 = do
    byte <- getWord8
    let compressed = testBit byte 0
        infinite = testBit byte 1
    if infinite then do
        skip (if compressed then wordCount @(Zp p) Prelude.* 2 Prelude.- 1 else wordCount @(Zp p) Prelude.* 4 Prelude.- 1)
        return InfCompressed
    else do
        let byteX1head = clearBit (clearBit (clearBit byte 0) 1) 2
        bytesX1tail <- replicateM (wordCount @(Zp p) Prelude.- 1) getWord8
        bytesX0 <- replicateM (wordCount @(Zp p)) getWord8
        let x1 = ofBytes (byteX1head:bytesX1tail)
            x0 = ofBytes bytesX0
            x = Ext2 x0 x1
            bigY = testBit byte 2
        if compressed then return (PointCompressed (Ext2 x0 x1) bigY)
        else do
            bytesY1 <- replicateM (wordCount @(Zp p)) getWord8
            bytesY0 <- replicateM (wordCount @(Zp p)) getWord8
            let y0 = ofBytes bytesY0
                y1 = ofBytes bytesY1
                y :: Ext2 (Zp p) i = Ext2 y0 y1
                bigY' = y Prelude.> negate y
            return (PointCompressed x bigY')
