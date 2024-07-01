{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Symbolic.Algorithms.Hash.Blake2b where

import           Data.Bits                                         ((.&.))
import qualified Data.Bits                                         as Bits
import qualified Data.Vector                                       as V
import           GHC.Natural                                       (Natural)
import qualified GHC.Num                                           as GHC
import           Prelude                                           (Eq (..), Functor (..), Int, Ord (..), error,
                                                                    fromIntegral, fst, otherwise, replicate, snd, take,
                                                                    ($), (.), (<$>))

import           ZkFold.Base.Algebra.Basic.Class                   (AdditiveGroup (..), AdditiveSemigroup (..),
                                                                    Exponent (..), FromConstant (..),
                                                                    MultiplicativeSemigroup (..), (-!))
import           ZkFold.Base.Algebra.Basic.Number                  (KnownNat, type (*), type (<=), value)
import           ZkFold.Symbolic.Algorithms.Hash.Blake2b.Constants (blake2b_iv, sigma)
import           ZkFold.Symbolic.Data.Bool                         (BoolType (..))
import           ZkFold.Symbolic.Data.ByteString                   (ByteString, Concat (..), ShiftBits (..),
                                                                    ToWords (..))
import           ZkFold.Symbolic.Data.Combinators                  (Extend (..), Iso (..), Shrink (..))
import           ZkFold.Symbolic.Data.UInt                         (UInt)

shiftUIntR :: forall n b a .
    ( Iso (UInt n b a) (ByteString n b a)
    , ShiftBits (ByteString n b a) ) => UInt n b a -> Natural -> UInt n b a
shiftUIntR u n = from @_ @(UInt n b a) $ from @_ @(ByteString n b a) u `shiftBitsR` n

xorUInt :: forall n a b . (BoolType (ByteString n b a), Iso (UInt n b a) (ByteString n b a)) =>
    UInt n b a ->  UInt n b a ->  UInt n b a
xorUInt u1 u2 = from @(ByteString n b a) @(UInt n b a) $ from u1 `xor` from u2

andUInt :: forall n a b . (BoolType (ByteString n b a), Iso (UInt n b a) (ByteString n b a)) =>
    UInt n b a ->  UInt n b a ->  UInt n b a
andUInt u1 u2 = from @(ByteString n b a) @(UInt n b a) $ from u1 && from u2

data Blake2b_224
data Blake2b_256

type Blake2bByteString b a =
    ( Extend (UInt 8 b a) (UInt 64 b a)
    , AdditiveSemigroup (UInt 64 b a)
    , Iso (UInt 64 b a) (ByteString 64 b a)
    , ShiftBits (ByteString 64 b a)
    , Exponent (UInt 64 b a) Natural
    , BoolType (ByteString 64 b a)
    , Shrink (UInt 64 b a) (UInt 8 b a)
    , AdditiveGroup (UInt 64 b a)
    , FromConstant Natural (UInt 64 b a)
    , FromConstant Natural (UInt 8 b a))

-- | Hash a `ByteString` using the Blake2b-224 hash function.
blake2b_224 :: forall inlen a backend .
    ( KnownNat inlen
    , ToWords (ByteString (inlen * 8) backend a) (ByteString 8 backend a)
    , Iso (UInt 8 backend a) (ByteString 8 backend a)
    , Concat (ByteString 8 backend a) (ByteString 224 backend a)
    , Blake2bByteString backend a
    ) => ByteString (inlen * 8) backend a -> ByteString 224 backend a -- 28 * 8 = 224
blake2b_224 = blake2b_libsodium @28 @0 @inlen

-- | Hash a `ByteString` using the Blake2b-256 hash function.
blake2b_256 :: forall inlen a backend .
    ( KnownNat inlen
    , ToWords (ByteString (inlen * 8) backend a) (ByteString 8 backend a)
    , Iso (UInt 8 backend a) (ByteString 8 backend a)
    , Concat (ByteString 8 backend a) (ByteString 256 backend a)
    , Blake2bByteString backend a
    ) => ByteString (inlen * 8) backend a -> ByteString 256 backend a -- 32 * 8 = 256
blake2b_256 = blake2b_libsodium @32 @0 @inlen

blake2b_libsodium :: forall outlen keylen inlen a backend .
    ( KnownNat keylen
    , KnownNat outlen
    , KnownNat inlen
    , 1 <= outlen
    , outlen <= 64
    , ToWords (ByteString (inlen * 8) backend a) (ByteString 8 backend a)
    , Iso (UInt 8 backend a) (ByteString 8 backend a)
    , Concat (ByteString 8 backend a) (ByteString (outlen * 8) backend a)
    , Blake2bByteString backend a
    ) =>
    ByteString (inlen * 8) backend a -> ByteString (outlen * 8) backend a
blake2b_libsodium input =
    concat $ fmap (from @(UInt 8 backend a) @(ByteString 8 backend a)) $ V.toList $
        blake2b @backend @a
            V.empty
            (value @outlen)
            V.empty
            (value @keylen)
            (V.fromList $ fmap (from @(ByteString 8 backend a) @(UInt 8 backend a)) $ toWords input)
            (value @inlen)

-- | state context
data Blake2bCtx a b = Blake2bCtx
   { b :: V.Vector (UInt 8 b a)  -- input buffer 128
   , h :: V.Vector (UInt 64 b a) -- chained state 8
   , t :: (Natural, Natural)     -- total number of bytes
   , c :: Natural                -- pointer for b[]
   , d :: Natural                -- digest size
   }

-- | Cyclic right rotation.
rotr64 ::
    ( Exponent (UInt 64 b a) Natural
    , ShiftBits (ByteString 64 b a)
    , Iso (ByteString 64 b a) (UInt 64 b a)
    , BoolType (ByteString 64 b a) ) =>
    (UInt 64 b a, Natural) -> UInt 64 b a
rotr64 (x, y) = x `shiftUIntR` y `xorUInt` x ^ (64 -! y)

-- | Little-endian byte access.
b2b_get64 :: forall a b .
    ( Extend (UInt 8 b a) (UInt 64 b a)
    , Exponent (UInt 64 b a) Natural
    , BoolType (ByteString 64 b a)
    , Iso (ByteString 64 b a) (UInt 64 b a) ) =>
    V.Vector (UInt 8 b a) -> UInt 64 b a
b2b_get64 (fmap extend . V.toList -> [p0, p1, p2, p3, p4, p5, p6, p7]) =
    p0                   `xorUInt`
    p1 ^ (8  :: Natural) `xorUInt`
    p2 ^ (16 :: Natural) `xorUInt`
    p3 ^ (24 :: Natural) `xorUInt`
    p4 ^ (32 :: Natural) `xorUInt`
    p5 ^ (40 :: Natural) `xorUInt`
    p6 ^ (48 :: Natural) `xorUInt`
    p7 ^ (56 :: Natural)
b2b_get64 _ = error "impossible" {- v = extend $ V.head v -}

-- | Little-endian byte access.
b2b_g :: forall b a .
    ( AdditiveSemigroup (UInt 64 b a)
    , Exponent (UInt 64 b a) Natural
    , ShiftBits (ByteString 64 b a)
    , Iso (UInt 64 b a) (ByteString 64 b a)
    , BoolType (ByteString 64 b a) ) =>
    V.Vector (UInt 64 b a) -> (Int, Int, Int, Int, (UInt 64 b a), (UInt 64 b a)) -> V.Vector (UInt 64 b a)
b2b_g v (a, b, c, d, x, y) =
    let a1 = v V.! a + v V.! b + x             -- v[a] = v[a] + v[b] + x;         \
        d1 = rotr64 (v V.! d `xorUInt` a1, 32) -- v[d] = ROTR64(v[d] ^ v[a], 32); \
        c1 = v V.! c + d1                      -- v[c] = v[c] + v[d];             \
        b1 = rotr64 (v V.! b `xorUInt` c1, 24) -- v[b] = ROTR64(v[b] ^ v[c], 24); \
        a2 = a1 + b1 + y                       -- v[a] = v[a] + v[b] + y;         \
        d2 = rotr64 (d1 `xorUInt` a2, 16)      -- v[d] = ROTR64(v[d] ^ v[a], 16); \
        c2 = c1 + d2                           -- v[c] = v[c] + v[d];             \
        b2 = rotr64 (b1 `xorUInt` c2, 63)      -- v[b] = ROTR64(v[b] ^ v[c], 63); }
    in v V.// [(a, a2), (d, d2), (c, c2), (b, b2)]

-- | Compression function. "last" flag indicates last block.
blake2b_compress :: forall a b . (Blake2bByteString b a) =>
    Blake2bCtx a b -> Int -> V.Vector (UInt 64 b a)
blake2b_compress Blake2bCtx{b, h, t} last =
    let v'  = V.slice 0 8 h V.++ blake2b_iv -- init work variables
        v'' = v' V.// [ (12, v' V.! 12 `xorUInt` (fromConstant $ fst t))  -- low 64 bits of offset
                      , (13, v' V.! 12 `xorUInt` (fromConstant $ snd t))] -- high 64 bits

        v0 = if last == 0 then v''
            else v'' V.// [(14, negate $ v'' V.! 14)] -- last block flag set ?

        -- get little-endian words
        m = (\i -> b2b_get64 (V.slice (8 GHC.* i) 8 b)) <$> V.fromList [0..15]

        v1 = V.foldl round v0 $ V.fromList [0..11] -- twelve rounds
            where
                round w0 i = w8
                    where
                        w1 = b2b_g w0 (0, 4,  8, 12, m V.! (sigma V.! i V.! 0), m V.! (sigma V.! i V.! 1))
                        w2 = b2b_g w1 (1, 5,  9, 13, m V.! (sigma V.! i V.! 2), m V.! (sigma V.! i V.! 3))
                        w3 = b2b_g w2 (2, 6, 10, 14, m V.! (sigma V.! i V.! 4), m V.! (sigma V.! i V.! 5))
                        w4 = b2b_g w3 (3, 7, 11, 15, m V.! (sigma V.! i V.! 6), m V.! (sigma V.! i V.! 7))
                        w5 = b2b_g w4 (0, 5, 10, 15, m V.! (sigma V.! i V.! 8), m V.! (sigma V.! i V.! 9))
                        w6 = b2b_g w5 (1, 6, 11, 12, m V.! (sigma V.! i V.!10), m V.! (sigma V.! i V.!11))
                        w7 = b2b_g w6 (2, 7,  8, 13, m V.! (sigma V.! i V.!12), m V.! (sigma V.! i V.!13))
                        w8 = b2b_g w7 (3, 4,  9, 14, m V.! (sigma V.! i V.!14), m V.! (sigma V.! i V.!15))
    in fmap (\(i, hi) -> hi `xorUInt` (v1 V.! i) `xorUInt` (v1 V.! (i GHC.+ 8))) (V.zip (V.fromList [0..7]) h)

-- | Initialize the hashing context "ctx" with optional key "key".
--
-- 1 <= outlen <= 64 gives the digest size in bytes.
-- Secret key (also <= 64 bytes) is optional (keylen = 0).
blake2b_init :: Blake2bByteString b a => Natural -> V.Vector (UInt 8 b a) -> Natural -> Blake2bCtx a b
blake2b_init outlen _ keylen | keylen > 64 || outlen < 0 || outlen > 64 = error "blake2b_init failed"
blake2b_init outlen key keylen | otherwise =
    let ctx = Blake2bCtx zeroVec (blake2b_iv V.// [(0, h0)]) (0, 0) 0 outlen
            where
                {-
                for (i = keylen; i < 128; i++)      // zero input block
                    ctx->b[i] = 0;
                -}
                zeroVec = V.fromList $ replicate 128 $ fromConstant @Natural 0

                outlen' = fromConstant outlen
                keylen' = fromConstant keylen
                const   = fromConstant @Natural 0x01010000

                h0 = V.head blake2b_iv `xorUInt` const `xorUInt` (keylen' ^ (8 :: Natural)) `xorUInt` outlen'
    in if keylen > 0 then
        let Blake2bCtx b h t _ d = blake2b_update ctx key keylen
        in  Blake2bCtx b h t 128 d
       else ctx

-- | Add "inlen" bytes from "in" into the hash.
blake2b_update :: forall a b . Blake2bByteString b a =>
    Blake2bCtx a b -> V.Vector (UInt 8 b a) -> Natural -> Blake2bCtx a b
blake2b_update ctx in' inlen =
    let update ctx'@Blake2bCtx{c} in'i
          | c == 128  = bUpdate in'i $ bufferFull ctx'
          | c > 128 = error "wow"
          | otherwise = bUpdate in'i ctx'

        bUpdate in'i Blake2bCtx{b, h, t, c, d} = Blake2bCtx {b = b V.// [(fromIntegral c, in'i)], h, t, c = c + 1, d}

        bufferFull :: Blake2bCtx a b -> Blake2bCtx a b
        bufferFull Blake2bCtx{b, h, t, d} =
            let t0 = fst t + 128
                t' = if t0 < 128          -- carry overflow ?
                     then (t0, snd t)     -- mark last block offset
                     else (t0, snd t + 1) -- high word
                h' = blake2b_compress (Blake2bCtx b h t' 128 d) 0
            in Blake2bCtx b h' t' 0 d

        indexs = V.take (fromIntegral inlen) in'
    in V.foldl update ctx indexs

-- | Generate the message digest (size given in init).
-- Result placed in "out".
blake2b_final :: forall a b . Blake2bByteString b a =>
    Blake2bCtx a b -> V.Vector (UInt 8 b a) -> V.Vector (UInt 8 b a)
blake2b_final Blake2bCtx{b, h, t, c, d} out =
    let ctx' = Blake2bCtx b' h t' 128 d
            where
                t' = if fst t + c < c {- carry overflow ? -}
                     then (fst t + c, snd t) -- mark last block offset
                     else (fst t + c, snd t + 1) -- high word
                zeroVec = V.fromList $ replicate (128 GHC.- cInt) $ fromConstant @Natural 0 -- zero input block
                cInt    = fromIntegral c
                b'      = V.take cInt b V.++ zeroVec

        h' = blake2b_compress ctx' 1 -- final block flag = 1

        -- little endian convert and store
        convert i = shrink $
            (h' V.! (i `Bits.shiftR` 3)
                `shiftUIntR` (8 * ((fromIntegral @Int @Natural i) .&. 7)))
                    `andUInt` (fromConstant @Natural 0xFF) {- TODO shrink is enough? -}
        outlen'   = fromIntegral d
        indexs    = V.fromList $ take outlen' [0, 1..]
    in fmap convert indexs V.++ V.drop outlen' out

-- | Convenience function for all-in-one computation.
blake2b :: Blake2bByteString b a =>
    V.Vector (UInt 8 b a) -> Natural ->
        V.Vector (UInt 8 b a) -> Natural ->
            V.Vector (UInt 8 b a) -> Natural -> V.Vector (UInt 8 b a)
blake2b out outlen key keylen in' inlen =
    let ctx  = blake2b_init outlen key keylen
        ctx' = blake2b_update ctx in' inlen
    in blake2b_final ctx' out
