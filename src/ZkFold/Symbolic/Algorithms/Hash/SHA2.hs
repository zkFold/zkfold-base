{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Algorithms.Hash.SHA2 (sha2) where

import           Control.Monad                                  (forM_)
import           Data.Proxy                                     (Proxy (..))
import qualified Data.STRef                                     as ST
import           Data.Type.Bool                                 (If)
import qualified Data.Vector                                    as V
import qualified Data.Vector.Mutable                            as VM
import           GHC.TypeLits                                   (Symbol)
import           GHC.TypeNats                                   (Div, KnownNat (..), Natural, natVal, type (*),
                                                                 type (+), type (-), type (<=?))
import           Prelude                                        (Int, id, pure, zip, ($), (>>=))
import qualified Prelude                                        as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Algorithms.Hash.SHA2.Constants (sha224InitialHashes, sha256InitialHashes,
                                                                 sha384InitialHashes, sha512InitialHashes,
                                                                 word32RoundConstants, word64RoundConstants)
import           ZkFold.Symbolic.Data.Bool                      (BoolType (..))
import           ZkFold.Symbolic.Data.ByteString                (Append (..), ByteString (..), Grow (..),
                                                                 ShiftBits (..), ToWords (..), Truncate (..))

class AlgorithmSetup (algorithm :: Symbol) a where
    type WordSize algorithm :: Natural
    type ChunkSize algorithm :: Natural
    type ResultSize algorithm :: Natural
    initialHashes :: V.Vector (ByteString (WordSize algorithm) a)
    roundConstants :: V.Vector (ByteString (WordSize algorithm) a)
    truncateResult :: ByteString (8 * WordSize algorithm) a -> ByteString (ResultSize algorithm) a
    sigmaShifts :: (Natural, Natural, Natural, Natural, Natural, Natural)
    sumShifts :: (Natural, Natural, Natural, Natural, Natural, Natural)

instance (Finite a, FromConstant Natural a) => AlgorithmSetup "SHA256" a where
    type WordSize "SHA256" = 32
    type ChunkSize "SHA256" = 512
    type ResultSize "SHA256" = 256
    initialHashes = sha256InitialHashes
    roundConstants = word32RoundConstants
    truncateResult = id
    sigmaShifts = (7, 18, 3, 17, 19, 10)
    sumShifts = (2, 13, 22, 6, 11, 25)


instance (Finite a, FromConstant Natural a, Truncate (ByteString 256 a) (ByteString 224 a)) => AlgorithmSetup "SHA224" a where
    type WordSize "SHA224" = 32
    type ChunkSize "SHA224" = 512
    type ResultSize "SHA224" = 224
    initialHashes = sha224InitialHashes
    roundConstants = word32RoundConstants
    truncateResult = truncate
    sigmaShifts = (7, 18, 3, 17, 19, 10)
    sumShifts = (2, 13, 22, 6, 11, 25)

instance (Finite a, FromConstant Natural a) => AlgorithmSetup "SHA512" a where
    type WordSize "SHA512" = 64
    type ChunkSize "SHA512" = 1024
    type ResultSize "SHA512" = 512
    initialHashes = sha512InitialHashes
    roundConstants = word64RoundConstants
    truncateResult = id
    sigmaShifts = (1, 8, 7, 19, 61, 6)
    sumShifts = (28, 34, 39, 14, 18, 41)

instance (Finite a, FromConstant Natural a, Truncate (ByteString 512 a) (ByteString 384 a)) => AlgorithmSetup "SHA384" a where
    type WordSize "SHA384" = 64
    type ChunkSize "SHA384" = 1024
    type ResultSize "SHA384" = 384
    initialHashes = sha384InitialHashes
    roundConstants = word64RoundConstants
    truncateResult = truncate
    sigmaShifts = (1, 8, 7, 19, 61, 6)
    sumShifts = (28, 34, 39, 14, 18, 41)

instance (Finite a, FromConstant Natural a, Truncate (ByteString 512 a) (ByteString 224 a)) => AlgorithmSetup "SHA512/224" a where
    type WordSize "SHA512/224" = 64
    type ChunkSize "SHA512/224" = 1024
    type ResultSize "SHA512/224" = 224
    initialHashes = sha512InitialHashes
    roundConstants = word64RoundConstants
    truncateResult = truncate
    sigmaShifts = (1, 8, 7, 19, 61, 6)
    sumShifts = (28, 34, 39, 14, 18, 41)

instance (Finite a, FromConstant Natural a, Truncate (ByteString 512 a) (ByteString 256 a)) => AlgorithmSetup "SHA512/256" a where
    type WordSize "SHA512/256" = 64
    type ChunkSize "SHA512/256" = 1024
    type ResultSize "SHA512/256" = 256
    initialHashes = sha512InitialHashes
    roundConstants = word64RoundConstants
    truncateResult = truncate
    sigmaShifts = (1, 8, 7, 19, 61, 6)
    sumShifts = (28, 34, 39, 14, 18, 41)

type family NextMultiple (n :: Natural) (divisor :: Natural) :: Natural where
    NextMultiple n divisor = divisor * Div (n + divisor - 1) divisor

type family PaddedLength (msg :: Natural) (block :: Natural) :: Natural where
    PaddedLength msg block = If (NextMultiple msg block - msg <=? 64) (block + NextMultiple msg block) (NextMultiple msg block)

sha2Pad
    :: forall (padTo :: Natural) (k :: Natural) a
    .  KnownNat padTo
    => KnownNat k
    => KnownNat (PaddedLength k padTo)
    => Finite a
    => FromConstant Natural a
    => ShiftBits (ByteString (PaddedLength k padTo) a)
    => AdditiveSemigroup (ByteString (PaddedLength k padTo) a)
    => Grow (ByteString k a) (ByteString (PaddedLength k padTo) a)
    => ByteString k a -> ByteString (PaddedLength k padTo) a
sha2Pad bs = grown + fromConstant padValue
    where
        l :: Natural
        l = natVal $ Proxy @k

        diff :: Natural
        diff = (natVal $ Proxy @(PaddedLength k padTo)) -! (natVal $ Proxy @k)

        padValue :: Natural
        padValue = 2 P.^ (diff -! 1) P.+ l

        grown :: ByteString (PaddedLength k padTo) a
        grown = grow bs `shiftBitsL` diff


sha2
    :: forall algorithm element k
    .  AlgorithmSetup algorithm element
    => KnownNat k
    => Finite element
    => FromConstant Natural element
    => KnownNat (ChunkSize algorithm)
    => KnownNat (PaddedLength k (ChunkSize algorithm))
    => AdditiveSemigroup (ByteString (WordSize algorithm) element)
    => BoolType (ByteString (WordSize algorithm) element)
    => ShiftBits (ByteString (WordSize algorithm) element)
    => ShiftBits (ByteString (PaddedLength k (ChunkSize algorithm)) element)
    => Grow (ByteString k element) (ByteString (PaddedLength k (ChunkSize algorithm)) element)
    => AdditiveSemigroup (ByteString (PaddedLength k (ChunkSize algorithm)) element)
    => ToWords (ByteString (ChunkSize algorithm) element) (ByteString (WordSize algorithm) element)
    => Append (ByteString (WordSize algorithm) element) (ByteString (8 * WordSize algorithm) element)
    => ToWords (ByteString (PaddedLength k (ChunkSize algorithm)) element) (ByteString (ChunkSize algorithm) element)
    => ByteString k element -> ByteString (ResultSize algorithm) element
sha2 messageBits = truncateResult @algorithm @element $ append $ V.toList hashParts
    where
        paddedMessage = sha2Pad @(ChunkSize algorithm) messageBits

        chunks :: [ByteString (ChunkSize algorithm) element]
        chunks = toWords paddedMessage

        rounds :: Int
        rounds = V.length $ roundConstants @algorithm @element

        hashParts :: V.Vector (ByteString (WordSize algorithm) element)
        hashParts = V.create $ do
            hn <- V.thaw $ initialHashes @algorithm @element

            forM_ chunks $ \chunk -> do
                let words = toWords @(ByteString (ChunkSize algorithm) element) @(ByteString (WordSize algorithm) element) chunk
                messageSchedule <- VM.unsafeNew @_ @(ByteString (WordSize algorithm) element) rounds
                forM_ (zip [0..] words) $ \(ix, w) -> VM.write messageSchedule ix w

                forM_ [16 .. rounds P.- 1] $ \ix -> do
                    w16 <- messageSchedule `VM.read` (ix P.- 16)
                    w15 <- messageSchedule `VM.read` (ix P.- 15)
                    w7  <- messageSchedule `VM.read` (ix P.- 7)
                    w2  <- messageSchedule `VM.read` (ix P.- 2)
                    let (sh0, sh1, sh2, sh3, sh4, sh5) = sigmaShifts @algorithm @element
                        s0  = (w15 `rotateBitsR` sh0) `xor` (w15 `rotateBitsR` sh1) `xor` (w15 `shiftBitsR` sh2)
                        s1  = (w2 `rotateBitsR` sh3) `xor` (w15 `rotateBitsR` sh4) `xor` (w15 `shiftBitsR` sh5)
                    VM.write messageSchedule ix $ w16 + s0 + w7 + s1

                aRef <- hn `VM.read` 0 >>= ST.newSTRef
                bRef <- hn `VM.read` 1 >>= ST.newSTRef
                cRef <- hn `VM.read` 2 >>= ST.newSTRef
                dRef <- hn `VM.read` 3 >>= ST.newSTRef
                eRef <- hn `VM.read` 4 >>= ST.newSTRef
                fRef <- hn `VM.read` 5 >>= ST.newSTRef
                gRef <- hn `VM.read` 6 >>= ST.newSTRef
                hRef <- hn `VM.read` 7 >>= ST.newSTRef

                forM_ [0 .. rounds P.- 1] $ \ix -> do
                    a <- ST.readSTRef aRef
                    b <- ST.readSTRef bRef
                    c <- ST.readSTRef cRef
                    d <- ST.readSTRef dRef
                    e <- ST.readSTRef eRef
                    f <- ST.readSTRef fRef
                    g <- ST.readSTRef gRef
                    h <- ST.readSTRef hRef

                    let ki = roundConstants @algorithm V.! ix
                    wi <- messageSchedule `VM.read` ix

                    let (sh0, sh1, sh2, sh3, sh4, sh5) = sumShifts @algorithm @element
                        s1 = (e `rotateBitsR` sh3) `xor` (e `rotateBitsR` sh4) `xor` (e `rotateBitsR` sh5)
                        ch = (e && f) `xor` (not e && g)
                        temp1 = h + s1 + ch + ki + wi
                        s0 = (a `rotateBitsR` sh0) `xor` (a `rotateBitsR` sh1) `xor` (a `rotateBitsR` sh2)
                        maj = (a && b) `xor` (a && c) `xor` (b && c)
                        temp2 = s0 + maj

                    ST.writeSTRef hRef g
                    ST.writeSTRef gRef f
                    ST.writeSTRef fRef e
                    ST.writeSTRef eRef $ d + temp1
                    ST.writeSTRef dRef c
                    ST.writeSTRef cRef b
                    ST.writeSTRef bRef a
                    ST.writeSTRef aRef $ temp1 + temp2

                a <- ST.readSTRef aRef
                b <- ST.readSTRef bRef
                c <- ST.readSTRef cRef
                d <- ST.readSTRef dRef
                e <- ST.readSTRef eRef
                f <- ST.readSTRef fRef
                g <- ST.readSTRef gRef
                h <- ST.readSTRef hRef

                VM.modify hn (+a) 0
                VM.modify hn (+b) 1
                VM.modify hn (+c) 2
                VM.modify hn (+d) 3
                VM.modify hn (+e) 4
                VM.modify hn (+f) 5
                VM.modify hn (+g) 6
                VM.modify hn (+h) 7

            pure hn
