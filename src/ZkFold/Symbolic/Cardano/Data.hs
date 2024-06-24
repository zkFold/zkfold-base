{-# LANGUAGE DerivingStrategies #-}
module ZkFold.Symbolic.Cardano.Data where

import           Codec.CBOR.Decoding      (Decoder)
import qualified Codec.CBOR.Decoding      as CBOR
import           Codec.CBOR.Encoding      (Encoding)
import qualified Codec.CBOR.Encoding      as CBOR
import qualified Codec.CBOR.Magic         as CBOR
import           Codec.Serialise          (Serialise (decode, encode))
import           Codec.Serialise.Decoding (decodeSequenceLenIndef, decodeSequenceLenN)
import           Control.Monad            (unless)
import           Data.Bits                (Bits (..))
import qualified Data.ByteString          as BS
import qualified Data.ByteString.Lazy     as BSL
import           Data.Word                (Word64, Word8)
import           Prelude                  (Applicative (..), Bounded (..), Eq (..), Foldable (..), Integer, Maybe (..),
                                           Monad (..), MonadFail (..), Monoid (..), Num (..), Ord (..), Semigroup (..),
                                           Show (..), flip, fromIntegral, otherwise, reverse, ($!), ($), (&&), (++),
                                           (.), (<$>))

data Data =
      Constr Integer [Data]
    | Map [(Data, Data)]
    | List [Data]
    | I Integer
    | B BS.ByteString
    deriving stock (Show, Eq, Ord)

instance Serialise Data where
    -- See Note [Encoding via Term]
    encode = encodeData
    decode = decodeData

-- | Turn Data into a CBOR Term.
encodeData :: Data -> Encoding
encodeData = \case
    -- See Note [CBOR alternative tags]
    Constr i ds | 0 <= i && i < 7   -> CBOR.encodeTag (fromIntegral (121 + i)) <> encode ds
    Constr i ds | 7 <= i && i < 128 -> CBOR.encodeTag (fromIntegral (1280 + (i - 7))) <> encode ds
    Constr i ds | otherwise         ->
        let tagEncoding =
              if fromIntegral (minBound @Word64) <= i && i <= fromIntegral (maxBound @Word64)
              then CBOR.encodeWord64 (fromIntegral i)
              -- This is a "correct"-ish encoding of the tag, but it will *not* deserialise, since
              -- we insist on a 'Word64' when we deserialise.
              -- So this is really a "soft" failure, without using 'error' or something.
              else CBOR.encodeInteger i
        in CBOR.encodeTag 102 <> CBOR.encodeListLen 2 <> tagEncoding <> encode ds
    Map es ->
      CBOR.encodeMapLen (fromIntegral $ length es) <>
        mconcat [ encode t <> encode t' | (t, t') <-es ]
    List ds                         -> encode ds
    I i                             -> encodeInteger i
    B b                             -> encodeBs b

-- Logic for choosing encoding borrowed from Codec.CBOR.Write
-- | Given an integer, create a 'CBOR.Term' that encodes it, following our size restrictions.
encodeInteger :: Integer -> Encoding
-- If it fits in a Word64, then it's less than 64 bytes for sure, and we can just send it off
-- as a normal integer for cborg to deal with
encodeInteger i | i >= 0 , i <= fromIntegral (maxBound :: Word64) = CBOR.encodeInteger i
                | i <  0 , i >= -1 - fromIntegral (maxBound :: Word64) = CBOR.encodeInteger i
-- Otherwise, it would be encoded as a bignum anyway, so we manually do the bignum
-- encoding with a bytestring inside, and since we use bsToTerm, that bytestring will
-- get chunked up if it's too big.
-- See Note [Evading the 64-byte limit]
encodeInteger i | i >= 0 = CBOR.encodeTag 2 <> encodeBs (integerToBytes i)
encodeInteger i | otherwise = CBOR.encodeTag 3 <> encodeBs (integerToBytes (-1 -i))

-- Taken exactly from Codec.CBOR.Write
integerToBytes :: Integer -> BS.ByteString
integerToBytes n0
  | n0 == 0   = BS.pack [0]
  | otherwise = BS.pack (reverse (go n0))
  where
    go n | n == 0    = []
         | otherwise = narrow n : go (n `shiftR` 8)

    narrow :: Integer -> Word8
    narrow = fromIntegral

-- | Given an bytestring, create a 'CBOR.Term' that encodes it, following our size restrictions.
encodeBs :: BS.ByteString -> Encoding
encodeBs b | BS.length b <= 64 = CBOR.encodeBytes b
-- It's a bit tricky to get cborg to emit an indefinite-length bytestring with chunks that we
-- control, so we encode it manually
-- See Note [Evading the 64-byte limit]
encodeBs b = CBOR.encodeBytesIndef <> foldMap encode (to64ByteChunks b) <> CBOR.encodeBreak

-- | Turns a 'BS.ByteString' into a list of <=64 byte chunks.
to64ByteChunks :: BS.ByteString -> [BS.ByteString]
to64ByteChunks b | BS.length b > 64 =
                   let (chunk, rest) = BS.splitAt 64 b
                   in chunk:to64ByteChunks rest
to64ByteChunks b = [b]

{- Note [Definite and indefinite forms of CBOR]
CBOR is annoying and you can have both definite (with a fixed length) and indefinite lists, maps,
etc.

So we have to be careful to handle both cases when decoding. When encoding we mostly don't make
the indefinite kinds, but see Note [Evading the 64-byte limit] for some cases where we do.
-}

-- | Turn a CBOR Term into Data if possible.
decodeData :: Decoder s Data
decodeData = CBOR.peekTokenType >>= \case
  -- These integers are at most 64 *bits*, so certainly less than 64 *bytes*
  CBOR.TypeUInt         -> I <$> CBOR.decodeInteger
  CBOR.TypeUInt64       -> I <$> CBOR.decodeInteger
  CBOR.TypeNInt         -> I <$> CBOR.decodeInteger
  CBOR.TypeNInt64       -> I <$> CBOR.decodeInteger
  -- See Note [The 64-byte limit]
  CBOR.TypeInteger      -> I <$> decodeBoundedBigInteger

  -- See Note [The 64-byte limit]
  CBOR.TypeBytes        -> B <$> decodeBoundedBytes
  CBOR.TypeBytesIndef   -> B . BSL.toStrict <$> decodeBoundedBytesIndef

  CBOR.TypeListLen      -> decodeList
  CBOR.TypeListLen64    -> decodeList
  CBOR.TypeListLenIndef -> decodeList

  CBOR.TypeMapLen       -> decodeMap
  CBOR.TypeMapLen64     -> decodeMap
  CBOR.TypeMapLenIndef  -> decodeMap

  CBOR.TypeTag          -> decodeConstr
  CBOR.TypeTag64        -> decodeConstr

  t                     -> fail ("Unrecognized value of type " ++ show t)

decodeBoundedBigInteger :: Decoder s Integer
decodeBoundedBigInteger = do
    tag <- CBOR.decodeTag
    -- Bignums contain a bytestring as the payload
    bs <- CBOR.peekTokenType >>= \case
        CBOR.TypeBytes      -> decodeBoundedBytes
        CBOR.TypeBytesIndef -> BSL.toStrict <$> decodeBoundedBytesIndef
        t                   -> fail ("Bignum must contain a byte string, got: " ++ show t)
    -- Depending on the tag, the bytestring is either a positive or negative integer
    case tag of
        2 -> pure $ CBOR.uintegerFromBytes bs
        3 -> pure $ CBOR.nintegerFromBytes bs
        t -> fail ("Bignum tag must be one of 2 or 3, got: " ++ show t)

-- Adapted from Codec.CBOR.Read
decodeBoundedBytesIndef :: Decoder s BSL.ByteString
decodeBoundedBytesIndef = CBOR.decodeBytesIndef >> decodeBoundedBytesIndefLen []

-- Adapted from Codec.CBOR.Read, to call the size-checking bytestring decoder
decodeBoundedBytesIndefLen :: [BS.ByteString] -> Decoder s BSL.ByteString
decodeBoundedBytesIndefLen acc = do
    stop <- CBOR.decodeBreakOr
    if stop then return $! BSL.fromChunks (reverse acc)
            else do !bs <- decodeBoundedBytes
                    decodeBoundedBytesIndefLen (bs : acc)

decodeBoundedBytes :: Decoder s BS.ByteString
decodeBoundedBytes =  do
  b <- CBOR.decodeBytes
  -- See Note [The 64-byte limit]
  unless (BS.length b <= 64) $ fail "ByteString exceeds 64 bytes"
  pure b

decodeList :: Decoder s Data
decodeList = List <$> decodeListOf decodeData

decodeListOf :: Decoder s x -> Decoder s [x]
decodeListOf decoder = CBOR.decodeListLenOrIndef >>= \case
  Nothing -> decodeSequenceLenIndef (flip (:)) [] reverse   decoder
  Just n  -> decodeSequenceLenN     (flip (:)) [] reverse n decoder

decodeMap :: Decoder s Data
decodeMap = CBOR.decodeMapLenOrIndef >>= \case
  Nothing -> Map <$> decodeSequenceLenIndef (flip (:)) [] reverse   decodePair
  Just n  -> Map <$> decodeSequenceLenN     (flip (:)) [] reverse n decodePair
  where
  decodePair = (,) <$> decodeData <*> decodeData

-- See Note [CBOR alternative tags] for the encoding scheme.
decodeConstr :: Decoder s Data
decodeConstr = CBOR.decodeTag64 >>= \case
  102 -> decodeConstrExtended
  t | 121 <= t && t < 128 ->
         Constr (fromIntegral t - 121) <$> decodeListOf decodeData
  t | 1280 <= t && t < 1401 ->
         Constr ((fromIntegral t - 1280) + 7) <$> decodeListOf decodeData
  t -> fail ("Unrecognized tag " ++ show t)
  where
  decodeConstrExtended = do
    len <- CBOR.decodeListLenOrIndef
    i <- CBOR.decodeWord64
    args <- decodeListOf decodeData
    case len of
      Nothing -> do
        done <- CBOR.decodeBreakOr
        unless done $ fail "Expected exactly two elements"
      Just n -> unless (n == 2) $ fail "Expected exactly two elements"
    pure $ Constr (fromIntegral i) args
