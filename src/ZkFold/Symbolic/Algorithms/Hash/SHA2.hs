{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module ZkFold.Symbolic.Algorithms.Hash.SHA2 (AlgorithmSetup (..), SHA2, sha2, SHA2N, sha2Natural) where

import           Control.DeepSeq                                (NFData, force)
import           Control.Monad                                  (forM_)
import           Data.Bits                                      (shiftL)
import           Data.Kind                                      (Type)
import           Data.Proxy                                     (Proxy (..))
import qualified Data.STRef                                     as ST
import           Data.Type.Bool                                 (If)
import           Data.Type.Equality                             (type (~))
import qualified Data.Vector                                    as V
import qualified Data.Vector.Mutable                            as VM
import           GHC.TypeLits                                   (Symbol)
import           GHC.TypeNats                                   (natVal, type (<=?))
import           Prelude                                        (Int, id, pure, zip, ($!), ($), (.), (>>=))
import qualified Prelude                                        as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector                        (Vector)
import           ZkFold.Symbolic.Algorithms.Hash.SHA2.Constants (sha224InitialHashes, sha256InitialHashes,
                                                                 sha384InitialHashes, sha512InitialHashes,
                                                                 sha512_224InitialHashes, sha512_256InitialHashes,
                                                                 word32RoundConstants, word64RoundConstants)
import           ZkFold.Symbolic.Class                          (Symbolic)
import           ZkFold.Symbolic.Data.Bool                      (BoolType (..))
import           ZkFold.Symbolic.Data.ByteString                (ByteString (..), Concat (..), ShiftBits (..),
                                                                 ToWords (..), Truncate (..))
import           ZkFold.Symbolic.Data.Combinators               (Extend (..), Iso (..), RegisterSize (..))
import           ZkFold.Symbolic.Data.UInt                      (UInt)

-- | SHA2 is a family of hashing functions with almost identical implementations but different constants and parameters.
-- This class links these varying parts with the appropriate algorithm.
--
class AlgorithmSetup (algorithm :: Symbol) (context :: (Type -> Type) -> Type) where
    type WordSize algorithm :: Natural
    -- ^ The length of words the algorithm operates internally, in bits.

    type ChunkSize algorithm :: Natural
    -- ^ Hashing algorithms from SHA2 family require splitting the input message into blocks.
    -- This type describes the size of these blocks, in bits.

    type ResultSize algorithm :: Natural
    -- ^ The length of the resulting hash, in bits.

    initialHashes :: V.Vector (ByteString (WordSize algorithm) context)
    -- ^ Initial hash values which will be mixed with the message bits.

    roundConstants :: V.Vector (ByteString (WordSize algorithm) context)
    -- ^ Constants used in the internal loop, one per each round.

    truncateResult :: ByteString (8 * WordSize algorithm) context -> ByteString (ResultSize algorithm) context
    -- ^ A function to postprocess the hash. For example, SHA224 requires dropping the last 32 bits of a SHA256 hash.

    sigmaShifts :: (Natural, Natural, Natural, Natural, Natural, Natural)
    -- ^ Round rotation values for Sigma in the internal loop.

    sumShifts :: (Natural, Natural, Natural, Natural, Natural, Natural)
    -- ^ Round rotation values for Sum in the internal loop.

instance Symbolic c => AlgorithmSetup "SHA256" c where
    type WordSize "SHA256" = 32
    type ChunkSize "SHA256" = 512
    type ResultSize "SHA256" = 256
    initialHashes = sha256InitialHashes
    roundConstants = word32RoundConstants
    truncateResult = id
    sigmaShifts = (7, 18, 3, 17, 19, 10)
    sumShifts = (2, 13, 22, 6, 11, 25)


instance Symbolic c => AlgorithmSetup "SHA224" c where
    type WordSize "SHA224" = 32
    type ChunkSize "SHA224" = 512
    type ResultSize "SHA224" = 224
    initialHashes = sha224InitialHashes
    roundConstants = word32RoundConstants
    truncateResult = truncate
    sigmaShifts = (7, 18, 3, 17, 19, 10)
    sumShifts = (2, 13, 22, 6, 11, 25)

instance Symbolic c => AlgorithmSetup "SHA512" c where
    type WordSize "SHA512" = 64
    type ChunkSize "SHA512" = 1024
    type ResultSize "SHA512" = 512
    initialHashes = sha512InitialHashes
    roundConstants = word64RoundConstants
    truncateResult = id
    sigmaShifts = (1, 8, 7, 19, 61, 6)
    sumShifts = (28, 34, 39, 14, 18, 41)

instance Symbolic c => AlgorithmSetup "SHA384" c where
    type WordSize "SHA384" = 64
    type ChunkSize "SHA384" = 1024
    type ResultSize "SHA384" = 384
    initialHashes = sha384InitialHashes
    roundConstants = word64RoundConstants
    truncateResult = truncate
    sigmaShifts = (1, 8, 7, 19, 61, 6)
    sumShifts = (28, 34, 39, 14, 18, 41)

instance Symbolic c => AlgorithmSetup "SHA512/224" c where
    type WordSize "SHA512/224" = 64
    type ChunkSize "SHA512/224" = 1024
    type ResultSize "SHA512/224" = 224
    initialHashes = sha512_224InitialHashes
    roundConstants = word64RoundConstants
    truncateResult = truncate
    sigmaShifts = (1, 8, 7, 19, 61, 6)
    sumShifts = (28, 34, 39, 14, 18, 41)

instance Symbolic c => AlgorithmSetup "SHA512/256" c where
    type WordSize "SHA512/256" = 64
    type ChunkSize "SHA512/256" = 1024
    type ResultSize "SHA512/256" = 256
    initialHashes = sha512_256InitialHashes
    roundConstants = word64RoundConstants
    truncateResult = truncate
    sigmaShifts = (1, 8, 7, 19, 61, 6)
    sumShifts = (28, 34, 39, 14, 18, 41)

-- | On type level, determine the smallest multiple of @divisor@ not less than @n@.
--
type family NextMultiple (n :: Natural) (divisor :: Natural) :: Natural where
    NextMultiple n divisor = divisor * Div (n + divisor - 1) divisor

{- | On type level, determine the length of the message after padding.
    Padding algorithm is described below:

    1. begin with the original message of length L bits
    2. append a single '1' bit
    3. append K '0' bits, where K is the minimum number >= 0 such that (L + 1 + K + 64) is a multiple of 512
    4. append L as a 64-bit big-endian integer, making the total post-processed length a multiple of 512 bits

    such that the bits in the message are: <original message of length L> 1 <K zeros> <L as 64 bit integer>

    For SHA384, SHA512 and SHA512/t, replace 512 with 1024 and 64 with 128.
-}
type family PaddedLength (msg :: Natural) (block :: Natural) (lenBits :: Natural) :: Natural where
    PaddedLength msg block lenBits = If (NextMultiple msg block - msg <=? lenBits) (block + NextMultiple msg block) (NextMultiple msg block)

-- | Constraints required for a type-safe SHA2
--
type SHA2 algorithm context k =
   ( AlgorithmSetup algorithm context
   , Symbolic context
   , KnownNat k
   , NFData (context (Vector (WordSize algorithm)))
   , KnownNat (ChunkSize algorithm)
   , KnownNat (WordSize algorithm)
   , KnownNat (PaddedLength k (ChunkSize algorithm) (2 * WordSize algorithm))
   , (Div (ChunkSize algorithm) (WordSize algorithm)) * (WordSize algorithm) ~ ChunkSize algorithm
   , (Div (PaddedLength k (ChunkSize algorithm) (2 * WordSize algorithm)) (ChunkSize algorithm)) * (ChunkSize algorithm) ~ PaddedLength k (ChunkSize algorithm) (2 * WordSize algorithm)
   , (Div (8 * (WordSize algorithm)) (WordSize algorithm)) * (WordSize algorithm) ~ 8 * (WordSize algorithm)
   , k <= PaddedLength k (ChunkSize algorithm) (2 * WordSize algorithm)
   )

-- | A generalised version of SHA2. It is agnostic of the ByteString base field.
-- Sample usage:
--
-- >>> bs = fromConstant (42 :: Natural) :: ByteString 8 (Zp BLS12_381_Scalar)
-- >>> hash = sha2 @"SHA256" bs
--
sha2
    :: forall (algorithm :: Symbol) context k
    .  SHA2 algorithm context k
    => ByteString k context -> ByteString (ResultSize algorithm) context
sha2 messageBits = sha2Blocks @algorithm @context chunks
    where
        paddedMessage :: ByteString (PaddedLength k (ChunkSize algorithm) (2 * WordSize algorithm)) context
        paddedMessage = sha2Pad @(ChunkSize algorithm) @(2 * WordSize algorithm) messageBits

        chunks :: [ByteString (ChunkSize algorithm) context]
        chunks = toWords paddedMessage

-- | Pad the input bytestring according to the rules described in @PaddedLength@
--
sha2Pad
    :: forall (padTo :: Natural) (lenBits :: Natural) context (k :: Natural)
    .  Symbolic context
    => KnownNat k
    => KnownNat (PaddedLength k padTo lenBits)
    => k <= PaddedLength k padTo lenBits
    => ByteString k context
    -> ByteString (PaddedLength k padTo lenBits) context
sha2Pad bs = grown || fromConstant padValue
    where
        l :: Natural
        l = natVal $ Proxy @k

        diff :: Natural
        diff = natVal (Proxy @(PaddedLength k padTo lenBits)) -! natVal (Proxy @k)

        padValue :: Natural
        padValue = 2 P.^ (diff -! 1) P.+ l

        grown :: ByteString (PaddedLength k padTo lenBits) context
        grown = extend bs `shiftBitsL` diff


-- | This allows us to calculate hash of a bytestring represented by a Natural number.
-- This is only useful for testing when the length of the test string is unknown at compile time.
-- This should not be exposed to users (and they probably won't find it useful anyway).
--
instance (KnownNat n, FromConstant Natural (ByteString n c)) => ToWords Natural (ByteString n c) where
    toWords = P.reverse . toWords'
        where
            toWords' :: Natural -> [ByteString n c]
            toWords' 0 = []
            toWords' n = fromConstant (n `mod` base) : toWords' (n `div` base)

            base :: Natural
            base = 2 P.^ (value @n)


-- | Constraints required for a SHA2 of a Natural number.
--
type SHA2N algorithm context =
   ( AlgorithmSetup algorithm context
    , Symbolic context
    , NFData (context (Vector (WordSize algorithm)))
    , KnownNat (ChunkSize algorithm)
    , KnownNat (WordSize algorithm)
    , (Div (ChunkSize algorithm) (WordSize algorithm)) * (WordSize algorithm) ~ ChunkSize algorithm
    , (Div (8 * (WordSize algorithm)) (WordSize algorithm)) * (WordSize algorithm) ~ 8 * (WordSize algorithm)
    )


-- | Same as @sha2@ but accepts a Natural number and length of message in bits instead of a ByteString.
-- Only used for testing.
--
sha2Natural
    :: forall (algorithm :: Symbol) (context :: (Type -> Type) -> Type)
    .  SHA2N algorithm context
    => Natural -> Natural -> ByteString (ResultSize algorithm) context
sha2Natural numBits messageBits = sha2Blocks @algorithm @context chunks
    where
        paddedMessage :: Natural
        paddedMessage = (messageBits `shiftL` diff) P.+ (1 `shiftL` (diff P.- 1)) P.+ numBits

        chunkSize :: Natural
        chunkSize = value @(ChunkSize algorithm)

        wordSize :: Natural
        wordSize = value @(WordSize algorithm)

        closestDivisor :: Natural
        closestDivisor = ((numBits P.+ chunkSize -! 1) `div` chunkSize) P.* chunkSize

        paddedLength :: Natural
        paddedLength
          | closestDivisor -! numBits P.<= (2 * wordSize) = closestDivisor P.+ chunkSize
          | P.otherwise = closestDivisor

        diff :: P.Int
        diff = P.fromIntegral $ paddedLength -! numBits

        chunks :: [ByteString (ChunkSize algorithm) context]
        chunks = toWords paddedMessage

-- | Internal loop of the SHA2 family algorithms.
--
-- A note on @force@: it is really necessary, otherwise the algorithm keeps piling up thunks.
-- Even 16 GB of RAM is not enough.
--
sha2Blocks
    :: forall algorithm (context :: (Type -> Type) -> Type)
    .  AlgorithmSetup algorithm context
    => Symbolic context
    => NFData (context (Vector (WordSize algorithm)))
    => KnownNat (WordSize algorithm)
    => (Div (ChunkSize algorithm) (WordSize algorithm)) * (WordSize algorithm) ~ ChunkSize algorithm
    => (Div (8 * (WordSize algorithm)) (WordSize algorithm)) * (WordSize algorithm) ~ 8 * (WordSize algorithm)
    => [ByteString (ChunkSize algorithm) context] -> ByteString (ResultSize algorithm) context
sha2Blocks chunks = truncateResult @algorithm @context $ concat $ V.toList hashParts
    where
        rounds :: Int
        rounds = V.length $ roundConstants @algorithm @context

        hashParts :: V.Vector (ByteString (WordSize algorithm) context)
        hashParts = V.create $ do
            !hn <- V.thaw $ initialHashes @algorithm @context

            forM_ chunks $ \chunk -> do
                let words = toWords @(ByteString (ChunkSize algorithm) context) @(ByteString (WordSize algorithm) context) chunk
                messageSchedule <- VM.unsafeNew @_ @(ByteString (WordSize algorithm) context) rounds
                forM_ (zip [0..] words) $ P.uncurry (VM.write messageSchedule)

                forM_ [16 .. rounds P.- 1] $ \ix -> do
                    !w16 <- messageSchedule `VM.read` (ix P.- 16)
                    !w15 <- messageSchedule `VM.read` (ix P.- 15)
                    !w7  <- messageSchedule `VM.read` (ix P.- 7)
                    !w2  <- messageSchedule `VM.read` (ix P.- 2)
                    let (sh0, sh1, sh2, sh3, sh4, sh5) = sigmaShifts @algorithm @context
                        s0  = force $ (w15 `rotateBitsR` sh0) `xor` (w15 `rotateBitsR` sh1) `xor` (w15 `shiftBitsR` sh2)
                        s1  = force $ (w2 `rotateBitsR` sh3) `xor` (w2 `rotateBitsR` sh4) `xor` (w2 `shiftBitsR` sh5)
                    VM.write messageSchedule ix $! from (from w16 + from s0 + from w7 + from s1 :: UInt (WordSize algorithm) Auto context)

                !aRef <- hn `VM.read` 0 >>= ST.newSTRef
                !bRef <- hn `VM.read` 1 >>= ST.newSTRef
                !cRef <- hn `VM.read` 2 >>= ST.newSTRef
                !dRef <- hn `VM.read` 3 >>= ST.newSTRef
                !eRef <- hn `VM.read` 4 >>= ST.newSTRef
                !fRef <- hn `VM.read` 5 >>= ST.newSTRef
                !gRef <- hn `VM.read` 6 >>= ST.newSTRef
                !hRef <- hn `VM.read` 7 >>= ST.newSTRef

                forM_ [0 .. rounds P.- 1] $ \ix -> do
                --forM_ [0 .. 1] $ \ix -> do
                    !a <- ST.readSTRef aRef
                    !b <- ST.readSTRef bRef
                    !c <- ST.readSTRef cRef
                    !d <- ST.readSTRef dRef
                    !e <- ST.readSTRef eRef
                    !f <- ST.readSTRef fRef
                    !g <- ST.readSTRef gRef
                    !h <- ST.readSTRef hRef

                    let ki = roundConstants @algorithm @context V.! ix
                    wi <- messageSchedule `VM.read` ix

                    let (sh0, sh1, sh2, sh3, sh4, sh5) = sumShifts @algorithm @context
                        s1    = force $ (e `rotateBitsR` sh3) `xor` (e `rotateBitsR` sh4) `xor` (e `rotateBitsR` sh5)
                        ch    = force $ (e && f) `xor` (not e && g)
                        temp1 = force $ from (from h + from s1 + from ch + from ki + from wi :: UInt (WordSize algorithm) Auto context) :: ByteString (WordSize algorithm) context
                        s0    = force $ (a `rotateBitsR` sh0) `xor` (a `rotateBitsR` sh1) `xor` (a `rotateBitsR` sh2)
                        maj   = force $ (a && b) `xor` (a && c) `xor` (b && c)
                        temp2 = force $ from (from s0 + from maj :: UInt (WordSize algorithm) Auto context) :: ByteString (WordSize algorithm) context

                    ST.writeSTRef hRef g
                    ST.writeSTRef gRef f
                    ST.writeSTRef fRef e
                    ST.writeSTRef eRef $ from (from d + from temp1 :: UInt (WordSize algorithm) Auto context)
                    ST.writeSTRef dRef c
                    ST.writeSTRef cRef b
                    ST.writeSTRef bRef a
                    ST.writeSTRef aRef $ from (from temp1 + from temp2 :: UInt (WordSize algorithm) Auto context)

                !a <- ST.readSTRef aRef
                !b <- ST.readSTRef bRef
                !c <- ST.readSTRef cRef
                !d <- ST.readSTRef dRef
                !e <- ST.readSTRef eRef
                !f <- ST.readSTRef fRef
                !g <- ST.readSTRef gRef
                !h <- ST.readSTRef hRef

                VM.modify hn (\w -> from (from w + from a :: UInt (WordSize algorithm) Auto context)) 0
                VM.modify hn (\w -> from (from w + from b :: UInt (WordSize algorithm) Auto context)) 1
                VM.modify hn (\w -> from (from w + from c :: UInt (WordSize algorithm) Auto context)) 2
                VM.modify hn (\w -> from (from w + from d :: UInt (WordSize algorithm) Auto context)) 3
                VM.modify hn (\w -> from (from w + from e :: UInt (WordSize algorithm) Auto context)) 4
                VM.modify hn (\w -> from (from w + from f :: UInt (WordSize algorithm) Auto context)) 5
                VM.modify hn (\w -> from (from w + from g :: UInt (WordSize algorithm) Auto context)) 6
                VM.modify hn (\w -> from (from w + from h :: UInt (WordSize algorithm) Auto context)) 7

            pure hn
