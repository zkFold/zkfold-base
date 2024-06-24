{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE TypeOperators        #-}

module ZkFold.Symbolic.Algorithms.Hash.Blake2b where

import           Data.Bits                                         (Bits (..))
import           Data.Word                                         (Word64)
import           Prelude                                           (Eq (..), Functor (..), Int, Num (..), Ord (..),
                                                                    error, fromIntegral, fst, otherwise, repeat, snd,
                                                                    undefined, ($), (.), (<$>), (||))

import           ZkFold.Base.Algebra.Basic.Number                  (KnownNat, type (*), type (<=), value)
import           ZkFold.Base.Data.Vector                           (Vector (..), fromVector)
import           ZkFold.Symbolic.Algorithms.Hash.Blake2b.Constants (blake2b_iv, sigma)
import           ZkFold.Symbolic.Data.ByteString                   (ByteString, Concat (..), ToWords (..))

data Blake2b_224
data Blake2b_256

-- | Hash a `ByteString` using the Blake2b-224 hash function.
blake2b_224 :: forall keylen a .
    ( KnownNat keylen
    , keylen <= 64
    , ToWords (ByteString (keylen * 8) a) (ByteString 8 a)
    , Concat (ByteString 8 a) (ByteString 224 a)
    ) => ByteString (keylen * 8) a -> ByteString 224 a -- 28 * 8 = 224
blake2b_224 = blake2b_libsodium @keylen @28

-- | Hash a `ByteString` using the Blake2b-256 hash function.
blake2b_256 :: forall keylen a . 
    ( KnownNat keylen
    , keylen <= 64
    , ToWords (ByteString (keylen * 8) a) (ByteString 8 a)
    , Concat (ByteString 8 a) (ByteString 256 a)
    ) => ByteString (keylen * 8) a -> ByteString 256 a -- 32 * 8 = 256
blake2b_256 = blake2b_libsodium @keylen @32

blake2b_libsodium :: forall keylen outlen a .
    ( KnownNat keylen
    , KnownNat outlen
    , keylen <= 64
    , 1 <= outlen
    , outlen <= 64
    , ToWords (ByteString (keylen * 8) a) (ByteString 8 a)
    , Concat (ByteString 8 a) (ByteString (outlen * 8) a)
    ) =>
    ByteString (keylen * 8) a -> ByteString (outlen * 8) a
blake2b_libsodium input = concat $ fromVector $ blake2b @keylen @outlen @a $ Vector @(keylen * 8) $ toWords input

-- | state context
data Blake2bCtx a = Blake2bCtx
   { b :: Vector 128 (ByteString 8 a)            -- input buffer 128
   , h :: Vector 8 (ByteString 64 a)             -- chained state 8
   , t :: ((ByteString 64 a), (ByteString 64 a)) -- total number of bytes
   , c :: (ByteString 64 a)                      -- pointer for b[]
   }
{-

-- | Cyclic right rotation.
rotr64 :: (Word64, Word64) -> Word64
rotr64 (x, y) = x `shiftR` fromIntegral y `xor` x `shiftL` (64 - fromIntegral y)

-- | Little-endian byte access.
b2b_get64 :: Vector 128 (ByteString 8 a) -> Word64
b2b_get64 (fmap fromIntegral . toList -> [p0, p1, p2, p3, p4, p5, p6, p7]) =
    p0             `xor`
    p1 `shiftL` 8  `xor`
    p2 `shiftL` 16 `xor`
    p3 `shiftL` 24 `xor`
    p4 `shiftL` 32 `xor`
    p5 `shiftL` 40 `xor`
    p6 `shiftL` 48 `xor`
    p7 `shiftL` 56
b2b_get64 _ = undefined

-- | Little-endian byte access.
b2b_g :: Vector 8 (ByteString 64 a) -> (Int, Int, Int, Int, Word64, Word64) -> Vector 8 (ByteString 64 a)
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
blake2b_compress :: Blake2bCtx a -> Int -> Vector 8 (ByteString 64 a)
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
        m = ((\i -> b2b_get64 (slice (8 * i) 8 b)) <$> fromList [0..15]) :: Vector 8 Word64

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
blake2b_init :: forall keylen outlen a .
    ( KnownNat keylen
    , KnownNat outlen
    , keylen <= 64
    , 1 <= outlen
    , outlen <= 64
    ) => Vector (keylen * 8) (ByteString 8 a) -> Blake2bCtx a
blake2b_init key = if value @keylen > 0 then ctx' else ctx
    where
        ctx = Blake2bCtx b h (0, 0) 0
            where
                b = take 128 (fromList $ repeat 0)
                h = blake2b_iv // [(0, b1)]
                    where
                        b1 = head blake2b_iv `xor` 0x01010000 `xor` fromIntegral (value @keylen * 8) `shiftL` 8 `xor` (value @outlen * 8)

        ctx' = Blake2bCtx b h t 128
            where
                Blake2bCtx b h t _ = blake2b_update ctx key

-- | Add "inlen" bytes from "key" into the hash.
blake2b_update :: forall keylen a .  KnownNat keylen => Blake2bCtx a -> Vector (keylen * 8) (ByteString 8 a) -> Blake2bCtx a
blake2b_update ctx in' = foldl f ctx (fromList [0..((value @keylen * 8)) - 1])
    where
        f :: Blake2bCtx a -> Int -> Blake2bCtx a
        f ctx'@Blake2bCtx{b, h, t, c} i
          | c == 128 = bufferFull ctx' -- buffer full ?
          | otherwise = Blake2bCtx {b = b // [(fromIntegral c + 1, in'!i)], h, t, c = c + 1}

        bufferFull :: Blake2bCtx a -> Blake2bCtx a
        bufferFull Blake2bCtx{b, h, t, c} = Blake2bCtx b h' t' 0
            where
                t' = if fst t + c < c {- carry overflow ? -}
                     then (fst t + c, snd t) -- mark last block offset
                     else (fst t + c, snd t + 1) -- high word
                h' = blake2b_compress (Blake2bCtx b h t' c) 0

-- | Generate the message digest (size given in init).
-- Result placed in "out".
blake2b_final :: forall outlen a .
    ( KnownNat outlen
    , 1 <= outlen
    , outlen <= 64
    ) => Blake2bCtx a -> Vector outlen (ByteString 8 a)
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
-}

blake2b_init :: forall keylen outlen a .
    ( KnownNat keylen
    , KnownNat outlen
    , keylen <= 64
    , 1 <= outlen
    , outlen <= 64
    ) => Vector (keylen * 8) (ByteString 8 a) -> Blake2bCtx a
blake2b_init = undefined

blake2b_final :: forall outlen a .
    ( KnownNat outlen
    , 1 <= outlen
    , outlen <= 64
    ) => Blake2bCtx a -> Vector outlen (ByteString 8 a)
blake2b_final = undefined

-- | Convenience function for all-in-one computation.
blake2b :: forall keylen outlen a .
    ( KnownNat keylen
    , KnownNat outlen
    , keylen <= 64
    , 1 <= outlen
    , outlen <= 64
    ) => Vector (keylen * 8) (ByteString 8 a) -> Vector outlen (ByteString 8 a)
blake2b key = blake2b_final @outlen $ blake2b_init @keylen @outlen key
