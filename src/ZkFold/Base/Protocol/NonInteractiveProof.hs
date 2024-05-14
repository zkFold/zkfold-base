{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Base.Protocol.NonInteractiveProof where

import           Crypto.Hash.SHA256          (hash)
import           Data.ByteString             (ByteString, cons, empty)
import           Data.Maybe                  (fromJust, fromMaybe)
import           Numeric.Natural             (Natural)
import           Prelude

import           ZkFold.Base.Data.ByteString

class Monoid t => ToTranscript t a where
    toTranscript :: a -> t

instance Binary a => ToTranscript ByteString a where
    toTranscript = toByteString

transcript :: ToTranscript t a => t -> a -> t
transcript ts a = ts <> toTranscript a

class Monoid t => FromTranscript t a where
    newTranscript  :: t -> t
    fromTranscript :: t -> a

instance Binary a => FromTranscript ByteString a where
    newTranscript  = cons 0
    fromTranscript = fromJust . fromByteString . hash

challenge :: forall t a . FromTranscript t a => t -> (a, t)
challenge ts =
    let ts' = newTranscript @t @a ts
    in (fromTranscript ts', ts')

challenges :: FromTranscript t a => t -> Natural -> ([a], t)
challenges ts0 n = go ts0 n []
  where
    go ts 0 acc = (acc, ts)
    go ts k acc =
        let (c, ts') = challenge ts
        in go ts' (k - 1) (c : acc)

class NonInteractiveProof a where
    type Transcript a

    type Setup a

    type Witness a

    type Input a

    type Proof a

    setup :: a -> Setup a

    prove :: Setup a -> Witness a -> (Input a, Proof a)

    verify :: Setup a -> Input a -> Proof a -> Bool

proveAPI :: forall a . (NonInteractiveProof a, Binary (Setup a), Binary (Witness a), Binary (Input a), Binary (Proof a)) => ByteString -> ByteString -> ByteString
proveAPI bsS bsW = fromMaybe empty $ do
    s <- fromByteString bsS
    w <- fromByteString bsW
    return $ toByteString $ prove @a s w
