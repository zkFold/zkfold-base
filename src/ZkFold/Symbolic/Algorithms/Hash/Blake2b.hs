{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module ZkFold.Symbolic.Algorithms.Hash.Blake2b where

import           Data.Bool                                         (bool)
import           Data.Constraint.Nat
import           Data.List                                         (foldl')
import           Data.Ratio                                        ((%))
import           Data.Vector                                       ((!), (//))
import qualified Data.Vector                                       as V
import           GHC.IsList                                        (IsList (..))
import qualified GHC.Num                                           as GHC
import           Prelude                                           hiding (Num (..), concat, divMod, length, mod,
                                                                    replicate, splitAt, truncate, (!!), (&&), (^))

import           ZkFold.Base.Algebra.Basic.Class                   (AdditiveGroup (..), AdditiveSemigroup (..),
                                                                    Exponent (..), FromConstant (..),
                                                                    MultiplicativeSemigroup (..), SemiEuclidean (..),
                                                                    divMod, one, zero, (-!))
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Data.Vector                           as Vec
import           ZkFold.Prelude                                    (length, replicate, splitAt, (!!))
import           ZkFold.Symbolic.Algorithms.Hash.Blake2b.Constants (blake2b_iv, sigma)
import           ZkFold.Symbolic.Class                             (Symbolic)
import           ZkFold.Symbolic.Data.Bool                         (BoolType (..))
import           ZkFold.Symbolic.Data.ByteString                   (ByteString (..), ShiftBits (..), Truncate (..),
                                                                    concat, reverseEndianness, toWords)
import           ZkFold.Symbolic.Data.Combinators                  (Iso (..), RegisterSize (..), extend)
import           ZkFold.Symbolic.Data.UInt                         (UInt (..))
import           Data.Constraint
import           Data.Constraint.Unsafe


-- TODO: This module is not finished yet. The hash computation is not correct.

-- | BLAKE2b Cryptographic hash. Reference:
-- https://tools.ietf.org/html/rfc7693


pow2 :: forall a . FromConstant Natural a => Natural -> a
pow2 = fromConstant @Natural . (2 ^)

shiftUIntR :: forall b . Symbolic b => UInt 64 Auto b -> Natural -> UInt 64 Auto b
shiftUIntR u n = from @_ @(UInt 64 Auto b) $ from @_ @(ByteString 64 b) u `shiftBitsR` n

shiftUIntL :: forall b . Symbolic b => UInt 64 Auto b -> Natural -> UInt 64 Auto b
shiftUIntL u n = u * pow2 n

xorUInt :: forall c . Symbolic c => UInt 64 Auto c ->  UInt 64 Auto c ->  UInt 64 Auto c
xorUInt u1 u2 = from @(ByteString 64 c) @(UInt 64 Auto c) $ from u1 `xor` from u2

-- | state context
data Blake2bCtx c = Blake2bCtx
   { h :: V.Vector (UInt 64 Auto c) -- chained state 8
   , m :: V.Vector (UInt 64 Auto c) -- input buffer 16
   , t :: (Natural, Natural)     -- total number of bytes
   }

-- | Cyclic right rotation.
rotr64 :: Symbolic c => (UInt 64 Auto c, Natural) -> UInt 64 Auto c
rotr64 (x, y) = (x `shiftUIntR` y) `xorUInt` (x `shiftUIntL` (64 -! y))

-- | Little-endian byte access.
b2b_g :: forall c . Symbolic c =>
    V.Vector (UInt 64 Auto c) -> (Int, Int, Int, Int, UInt 64 Auto c, UInt 64 Auto c) -> V.Vector (UInt 64 Auto c)
b2b_g v (a, b, c, d, x, y) =
    let va1 = (v ! a) + (v ! b) + x                 -- v[a] = v[a] + v[b] + x;         \
        vd1 = rotr64 ((v ! d) `xorUInt` va1, 32)    -- v[d] = ROTR64(v[d] ^ v[a], 32); \
        vc1 = (v ! c) + vd1                         -- v[c] = v[c] + v[d];             \
        vb1 = rotr64 ((v ! b) `xorUInt` vc1, 24)    -- v[b] = ROTR64(v[b] ^ v[c], 24); \
        va2 = va1 + vb1 + y                         -- v[a] = v[a] + v[b] + y;         \
        vd2 = rotr64 (vd1 `xorUInt` va2, 16)        -- v[d] = ROTR64(v[d] ^ v[a], 16); \
        vc2 = vc1 + vd2                             -- v[c] = v[c] + v[d];             \
        vb2 = rotr64 (vb1 `xorUInt` vc2, 63)        -- v[b] = ROTR64(v[b] ^ v[c], 63);
    in v // [(a, va2), (b, vb2), (c, vc2), (d, vd2)]

-- | Compression function. "last" flag indicates the last block.
blake2b_compress :: forall c . Symbolic c => Blake2bCtx c -> Bool -> V.Vector (UInt 64 Auto c)
blake2b_compress Blake2bCtx{h, m, t} lastBlock =
    let v'  = h V.++ blake2b_iv -- init work variables
        v'' = v' V.// [ (12, (v' ! 12) `xorUInt` fromConstant (fst t))  -- low word of the offset
                      , (13, (v' ! 13) `xorUInt` fromConstant (snd t))] -- high word of the offset

        v0 = if lastBlock                                               -- last block flag set ?
                then v'' // [(14, (v'' ! 14) `xorUInt` negate one)]     -- Invert all bits
                else v''

        hashRound w0 i = w8
            where
                s  = sigma ! i
                w1 = b2b_g w0 (0, 4,  8, 12, m ! (s ! 0),  m ! (s ! 1))
                w2 = b2b_g w1 (1, 5,  9, 13, m ! (s ! 2),  m ! (s ! 3))
                w3 = b2b_g w2 (2, 6, 10, 14, m ! (s ! 4),  m ! (s ! 5))
                w4 = b2b_g w3 (3, 7, 11, 15, m ! (s ! 6),  m ! (s ! 7))
                w5 = b2b_g w4 (0, 5, 10, 15, m ! (s ! 8),  m ! (s ! 9))
                w6 = b2b_g w5 (1, 6, 11, 12, m ! (s ! 10), m ! (s ! 11))
                w7 = b2b_g w6 (2, 7,  8, 13, m ! (s ! 12), m ! (s ! 13))
                w8 = b2b_g w7 (3, 4,  9, 14, m ! (s ! 14), m ! (s ! 15))

        v1 = V.foldl hashRound v0 $ fromList [0..11] -- twelve rounds
    in fmap (\(i, hi) -> hi `xorUInt` (v1 ! i) `xorUInt` (v1 ! (i GHC.+ 8))) (V.zip (fromList [0..7]) h)

blake2b' :: forall bb' kk' ll' nn' c .
    ( Symbolic c
    , KnownNat bb'
    , KnownNat kk'
    , KnownNat ll'
    , KnownNat nn'
    , 8 * nn' <= 512
    ) => [V.Vector (UInt 64 Auto c)] -> ByteString (8 * nn') c
blake2b' d =
    let bb = value @bb'
        ll = value @ll'
        kk = value @kk'
        nn = value @nn'
        dd = bool (ceiling (kk % bb) + ceiling (ll % bb)) 1 (kk == 0 && ll == 0) :: Natural

        toOffset :: forall x . (FromConstant Natural x) => Natural -> (x, x)
        toOffset x = let (hi, lo) = x `divMod` pow2 64 in (fromConstant lo, fromConstant hi)

        h = blake2b_iv :: V.Vector (UInt 64 Auto c)

        -- Parameter block p[0]
        h' = h // [(0, (h ! 0) `xorUInt` fromConstant @Natural 0x01010000 `xorUInt` (fromConstant kk `shiftUIntR` 8) `xorUInt` fromConstant nn)]

        -- Process padded key and data blocks
        h'' = if dd > 1
            then foldl' (\acc i -> blake2b_compress (Blake2bCtx acc (d !! i) (toOffset @Natural $ (i + 1) * bb)) False) h' [0 .. dd -! 2]
            else h'

        -- Final round
        h''' = if kk == 0
            then blake2b_compress (Blake2bCtx h'' (d !! (dd -! 1)) (toOffset @Natural $ ll)) True
            else blake2b_compress (Blake2bCtx h'' (d !! (dd -! 1)) (toOffset @Natural $ ll + bb)) True

        bs = reverseEndianness @64 $ concat @8 @64 $ Vec.unsafeToVector @8 $ map from $ toList h''' :: ByteString (64 * 8) c
    in with8n @nn' (truncate bs)

type ExtensionBits inputLen = 8 * (128 - Mod inputLen 128)
type ExtendedInputByteString inputLen c = ByteString (8 * inputLen + ExtensionBits inputLen) c

withExtensionBits :: forall n {r}. KnownNat n => (KnownNat (8 * (128 - Mod n 128)) => r) -> r
withExtensionBits = withDict (modBound @n @128) $
                        withDict (modNat @n @128) $
                            withDict (minusNat @128 @(Mod n 128)) $
                                withDict (timesNat @8 @(128 - Mod n 128))

withExtendedInputByteString :: forall n {r}. KnownNat n => (KnownNat (8 * n + 8 * (128 - Mod n 128)) => r) -> r
withExtendedInputByteString = withExtensionBits @n $
                                    withDict (timesNat @8 @n) $
                                        withDict (plusNat @(8 * n) @( 8 * (128 - Mod n 128)))

with8nLessExt :: forall n {r}. KnownNat n => (8 * n <= 8 * n +  8 * (128 - Mod n 128) => r) -> r
with8nLessExt = withExtendedInputByteString @n $
                    withDict (zeroLe @( 8 * (128 - Mod n 128))) $
                        withDict (plusMonotone2 @(8 * n) @0 @( 8 * (128 - Mod n 128)))

with8n  :: forall n {r}. KnownNat n => (KnownNat (8 * n) => r) -> r
with8n = withDict (timesNat @8 @n)

black2bDivConstraint :: forall a b. (Gcd a 8 ~ 8) :- (Div (8 * a + 8 * (2 * 64 - Mod a (2 * b))) 64 * 64 ~ 8 * a + 8 * (2 * 64 - Mod a (2 * 64)) )
black2bDivConstraint = Sub unsafeAxiom

withBlack2bDivConstraint :: forall a b {r}. (Gcd a 8 ~ 8) => (Div (8 * a + 8 * (2 * 64 - Mod a (2 * b))) 64 * 64 ~ 8 * a + 8 * (2 * 64 - Mod a (2 * 64)) => r) -> r
withBlack2bDivConstraint =  withDict (black2bDivConstraint @a @b)


blake2b :: forall keyLen inputLen outputLen c n.
    ( Symbolic c
    , KnownNat keyLen
    , KnownNat inputLen
    , KnownNat outputLen
    , Gcd inputLen 8 ~ 8
    , n ~ (8 * inputLen + ExtensionBits inputLen)
    , 8 * outputLen <= 512
    ) => Natural -> ByteString (8 * inputLen) c -> ByteString (8 * outputLen) c
blake2b key input =
    let input' = with8nLessExt @inputLen $ withExtendedInputByteString @inputLen $ with8n @inputLen $ withBlack2bDivConstraint @inputLen @64 $
                    Vec.parFmap from $ toWords @(Div n 64) @64 $
                    reverseEndianness @64 $
                    flip (withExtendedInputByteString @inputLen $ rotateBitsL) (withExtensionBits @inputLen $ value @(ExtensionBits inputLen)) $
                    extend @_ @(ExtendedInputByteString inputLen c) input :: Vec.Vector (Div n 64) (UInt 64 Auto c)

        key'    = fromConstant @_ key :: UInt 64 Auto c
        input'' = if value @keyLen > 0
            then key' : Vec.fromVector input'
            else Vec.fromVector input'

        padding = length input'' `mod` 16
        input''' = input'' ++ replicate (16 -! padding) zero

        toBlocks :: [w] -> [V.Vector w]
        toBlocks [] = []
        toBlocks xs = let (a, b) = splitAt 16 xs in fromList a : toBlocks b

        d = toBlocks input'''
    in blake2b'
        @128       -- block size bb'
        @keyLen    -- key length kk'
        @inputLen  -- input length ll'
        d

-- | Hash a `ByteString` using the Blake2b-224 hash function.
blake2b_224 :: forall inputLen c n.
    ( Symbolic c
    , KnownNat inputLen
    , Gcd inputLen 8 ~ 8
    , n ~ (8 * inputLen + ExtensionBits inputLen)
    ) => ByteString (8 * inputLen) c -> ByteString 224 c
blake2b_224 = blake2b @0 @inputLen @28 (fromConstant @Natural 0)

-- | Hash a `ByteString` using the Blake2b-256 hash function.
blake2b_256 :: forall inputLen c n .
    ( Symbolic c
    , KnownNat inputLen
    , n ~ (8 * inputLen + ExtensionBits inputLen)
    , Gcd inputLen 8 ~ 8
    ) => ByteString (8 * inputLen) c -> ByteString 256 c
blake2b_256 = blake2b @0 @inputLen @32 (fromConstant @Natural 0)

-- | Hash a `ByteString` using the Blake2b-256 hash function.
blake2b_512 :: forall inputLen c n .
    ( Symbolic c
    , KnownNat inputLen
    , n ~ (8 * inputLen + ExtensionBits inputLen)
    , Gcd inputLen 8 ~ 8
    ) => ByteString (8 * inputLen) c -> ByteString 512 c
blake2b_512 = blake2b @0 @inputLen @64 0
