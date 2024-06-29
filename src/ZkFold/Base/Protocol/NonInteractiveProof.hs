{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Base.Protocol.NonInteractiveProof where

import           Crypto.Hash.BLAKE2.BLAKE2b  (hash)
import           Data.ByteString             (ByteString, cons)
import           Data.Maybe                  (fromJust)
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
    fromTranscript = fromJust . fromByteString . hash 28 mempty

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

    type SetupProve a

    type SetupVerify a

    type Witness a

    type Input a

    type Proof a

    setupProve :: a -> SetupProve a

    setupVerify :: a -> SetupVerify a

    prove :: SetupProve a -> Witness a -> (Input a, Proof a)

    verify :: SetupVerify a -> Input a -> Proof a -> Bool

class (NonInteractiveProof a, NonInteractiveProof b) => CompatibleNonInteractiveProofs a b where
    nipProtocolTransform :: a -> b
    nipInputTransform    :: Input a -> Input b
    nipProofTransform    :: Proof a -> Proof b

nipCompatibility :: forall a b . CompatibleNonInteractiveProofs a b
    => a -> Witness a -> Bool
nipCompatibility a w =
    let b      = nipProtocolTransform @a @b a
        (i, p) = prove @a (setupProve a) w
        i'     = nipInputTransform @a @b i
        p'     = nipProofTransform @a @b p
    in verify @b (setupVerify b) i' p'

instance NonInteractiveProof a => CompatibleNonInteractiveProofs a a where
    nipProtocolTransform = id
    nipInputTransform    = id
    nipProofTransform    = id
