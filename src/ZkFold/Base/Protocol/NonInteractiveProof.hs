{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Base.Protocol.NonInteractiveProof where

import           Crypto.Hash.SHA256          (hash)
import           Data.ByteString             (ByteString, cons)
import           Data.Maybe                  (fromJust)
import           Data.Typeable               (Typeable)
import           Prelude
import           Test.QuickCheck             (Arbitrary)

import           ZkFold.Base.Data.ByteString (ToByteString(..), FromByteString (..))

class Monoid t => ToTranscript t a where
    toTranscript :: a -> t

instance ToByteString a => ToTranscript ByteString a where
    toTranscript = toByteString

transcript :: ToTranscript t a => t -> a -> t
transcript ts a = ts <> toTranscript a

class Monoid t => FromTranscript t a where
    newTranscript  :: t -> t
    fromTranscript :: t -> a

instance FromByteString a => FromTranscript ByteString a where
    newTranscript  = cons 0
    fromTranscript = fromJust . fromByteString . hash

challenge :: forall t a . FromTranscript t a => t -> (a, t)
challenge ts =
    let ts' = newTranscript @t @a ts
    in (fromTranscript ts', ts')

challenges :: FromTranscript t a => t -> Integer -> ([a], t)
challenges ts0 n = go ts0 n []
  where
    go ts 0 acc = (acc, ts)
    go ts k acc =
        let (c, ts') = challenge ts
        in go ts' (k - 1) (c : acc)

class (Arbitrary (Params a), Arbitrary (SetupSecret a), Arbitrary (ProverSecret a), Arbitrary (Witness a),
       Show (Setup a), Show (ProverSecret a), Show (Witness a), Typeable a)
        => NonInteractiveProof a where
    type Transcript a

    type Params a

    type SetupSecret a

    type Setup a

    type ProverSecret a

    type Witness a

    type Input a

    type Proof a

    setup :: Params a -> SetupSecret a -> Setup a

    prove :: ProverSecret a -> Setup a -> Witness a -> (Input a, Proof a)

    verify :: Setup a -> Input a -> Proof a -> Bool