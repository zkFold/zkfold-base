{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module ZkFold.Symbolic.Algorithms.Hash.Blake2b where

import           Data.Bits                                         (Bits (..))
import           Data.Vector                                       (Vector, foldl, fromList, head, slice, take, toList,
                                                                    zip, (!), (++), (//))
import           Data.Word                                         (Word64, Word8)
import           GHC.Natural                                       (Natural)
import           Prelude                                           (Eq (..), Functor (..), Int, Num (..),
                                                                    Ord (..), fromIntegral, fst, otherwise, repeat, snd,
                                                                    undefined, ($), (.), (<$>), (||), error)

import           ZkFold.Symbolic.Algorithms.Hash.Blake2b.Constants (blake2b_iv, blake2b_keybytes, blake2b_outbytes,
                                                                    sigma)
import           ZkFold.Symbolic.Cardano.Builtins                  (BuiltinByteString)
import           ZkFold.Symbolic.Data.ByteString                   (ByteString)

data Blake2b_224
data Blake2b_256

-- | Hash a `ByteString` using the Blake2b-224 hash function.
blake2b_224 :: Int -> BuiltinByteString -> ByteString 28 a -- 28 * 8 = 224
blake2b_224 = blake2b_libsodium 28

-- | Hash a `ByteString` using the Blake2b-256 hash function.
blake2b_256 :: Int -> BuiltinByteString -> ByteString 32 a -- 32 * 8 = 256
blake2b_256 = blake2b_libsodium 32

blake2b_libsodium :: forall a m . Natural -> Int -> BuiltinByteString -> ByteString m a
blake2b_libsodium size inputlen input = undefined
    where -- Vector 128 Word8 -> ByteString n a
          -- ByteString n a -> Vector 128 Word8
        inptr = undefined input
        outM = blake2b (fromIntegral size) inptr inputlen -- we used unkeyed hash

-- | state context
data Blake2bCtx = Blake2bCtx
   { b :: Vector Word8     -- input buffer 128
   , h :: Vector Word64    -- chained state 8
   , t :: (Word64, Word64) -- total number of bytes
   , c :: Word64           -- pointer for b[]
   }

-- | Cyclic right rotation.
rotr64 :: (Word64, Word64) -> Word64
rotr64 (x, y) = x `shiftR` fromIntegral y `xor` x `shiftL` (64 - fromIntegral y)

-- | Little-endian byte access.
b2b_get64 :: Vector Word8 -> Word64
b2b_get64 (fmap fromIntegral . toList -> [p0, p1, p2, p3, p4, p5, p6, p7]) =
    p0               `xor`
    p1 `shiftL` 8  `xor`
    p2 `shiftL` 16 `xor`
    p3 `shiftL` 24 `xor`
    p4 `shiftL` 32 `xor`
    p5 `shiftL` 40 `xor`
    p6 `shiftL` 48 `xor`
    p7 `shiftL` 56
b2b_get64 _ = undefined

-- | Little-endian byte access.
b2b_g :: Vector Word64 -> (Int, Int, Int, Int, Word64, Word64) -> Vector Word64
b2b_g v (a, b, c, d, x, y) = v // [(a, a2), (d, d2), (c, c2), (b, b2)]
    where
        a1 = v!a + v!b + x             -- v[a] = v[a] + v[b] + x;         \
        d1 = rotr64 (v!d `xor` a1, 32) -- v[d] = ROTR64(v[d] ^ v[a], 32); \
        c1 = v!c + d1                  -- v[c] = v[c] + v[d];             \
        b1 = rotr64 (v!b `xor` c1, 24) -- v[b] = ROTR64(v[b] ^ v[c], 24); \
        a2 = a1 + b1 + y               -- v[a] = v[a] + v[b] + y;         \
        d2 = rotr64 (d1 `xor` a2, 16)  -- v[d] = ROTR64(v[d] ^ v[a], 16); \
        c2 = c1 + d2                   -- v[c] = v[c] + v[d];             \
        b2 = rotr64 (b1 `xor` c2, 63)  -- v[b] = ROTR64(v[b] ^ v[c], 63); }

-- | Compression function. "last" flag indicates last block.
blake2b_compress :: Blake2bCtx -> Int -> Vector Word64
blake2b_compress Blake2bCtx{b, h, t} last = h'
    where
        v0 = if last == 0 then v''
            else v'' // [(14, complement $ v''!14)] -- last block flag set ?
            where
                v' = slice 0 8 h ++ blake2b_iv -- init work variables
                v'' = v' // [ (12, v'!12 `xor` fst t) {- low 64 bits of offset -}
                            , (13, v'!12 `xor` snd t) {- high 64 bits -}
                            ]
        -- get little-endian words
        m = ((\i -> b2b_get64 (slice (8 * i) 8 b)) <$> fromList [0..15]) :: Vector Word64

        v1 = foldl f v0 $ fromList [0..11] -- twelve rounds
            where
                f w0 i = w8
                    where
                        w1 = b2b_g w0 (0, 4,  8, 12, m!(sigma!i! 0), m!(sigma!i! 1))
                        w2 = b2b_g w1 (1, 5,  9, 13, m!(sigma!i! 2), m!(sigma!i! 3))
                        w3 = b2b_g w2 (2, 6, 10, 14, m!(sigma!i! 4), m!(sigma!i! 5))
                        w4 = b2b_g w3 (3, 7, 11, 15, m!(sigma!i! 6), m!(sigma!i! 7))
                        w5 = b2b_g w4 (0, 5, 10, 15, m!(sigma!i! 8), m!(sigma!i! 9))
                        w6 = b2b_g w5 (1, 6, 11, 12, m!(sigma!i!10), m!(sigma!i!11))
                        w7 = b2b_g w6 (2, 7,  8, 13, m!(sigma!i!12), m!(sigma!i!13))
                        w8 = b2b_g w7 (3, 4,  9, 14, m!(sigma!i!14), m!(sigma!i!15))

        h' = fmap (\(i, e) -> e `xor` v1!i `xor` v1!(i + 8)) (zip (fromList [0..7]) h)

-- | Initialize the hashing context "ctx" with optional key "key".
--
-- 1 <= outlen <= 64 gives the digest size in bytes.
-- Secret key (also <= 64 bytes) is optional (keylen = 0).
blake2b_init :: Word64 -> Vector Word8 -> Int -> Blake2bCtx
blake2b_init outlen key keylen
    | outlen <= 0 || outlen > blake2b_outbytes || keylen > blake2b_keybytes =
        error "blake2b_init: something went wrong: outlen <= 0 || outlen > blake2b_outbytes || keylen > blake2b_keybytes"
    | otherwise = if keylen > 0 then ctx' else ctx
    where
        ctx = Blake2bCtx b h (0, 0) 0
            where
                b = take 128 (fromList $ repeat 0)
                h = blake2b_iv // [(0, b1)]
                    where
                        b1 = head blake2b_iv `xor` 0x01010000 `xor` fromIntegral keylen `shiftL` 8 `xor` outlen

        ctx' = Blake2bCtx b h t 128
            where
                Blake2bCtx b h t _ = blake2b_update ctx key keylen

-- | Add "inlen" bytes from "key" into the hash.
blake2b_update :: Blake2bCtx -> Vector Word8 -> Int -> Blake2bCtx
blake2b_update ctx in' inlen = foldl f ctx (fromList [0..inlen - 1])
    where
        f :: Blake2bCtx -> Int -> Blake2bCtx
        f ctx'@Blake2bCtx{b, h, t, c} i
          | c == 128 = bufferFull ctx' -- buffer full ?
          | otherwise = Blake2bCtx {b = b // [(fromIntegral c + 1, in'!i)], h, t, c = c + 1}

        bufferFull :: Blake2bCtx -> Blake2bCtx
        bufferFull Blake2bCtx{b, h, t, c} = Blake2bCtx b h' t' 0
            where
                t' = if fst t + c < c {- carry overflow ? -}
                     then (fst t + c, snd t) -- mark last block offset
                     else (fst t + c, snd t + 1) -- high word
                h' = blake2b_compress (Blake2bCtx b h t' c) 0

-- | Generate the message digest (size given in init).
-- Result placed in "out".
blake2b_final :: Blake2bCtx -> Vector Word8
blake2b_final Blake2bCtx{b, h, t, c} = out'
    where
        ctx' = Blake2bCtx b' h t' 128
            where
                t' = if fst t + c < c {- carry overflow ? -}
                     then (fst t + c, snd t) -- mark last block offset
                     else (fst t + c, snd t + 1) -- high word
                b' = take (fromIntegral c) b ++ take (128 - fromIntegral c) (fromList $ repeat 0) -- zero input block

        -- little endian convert and store
        out' = fmap (\i -> fromIntegral $ h'!(i `shiftR` 3) `shiftR` (8 * (i .&. 7)) .&. 0xFF) indexs
            where
                indexs = take (fromIntegral c) $ fromList [0..]
                h' = blake2b_compress ctx' 1 -- final block flag = 1

-- | Convenience function for all-in-one computation.
blake2b :: Word64 -> Vector Word8 -> Int -> Vector Word8
blake2b outlen key keylen = blake2b_final $ blake2b_init outlen key keylen
