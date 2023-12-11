{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Base.Protocol.NonInteractiveProof where

import           Crypto.Hash.SHA256          (hash)
import           Data.ByteString             (ByteString, snoc)
import           Data.Maybe                  (fromJust)
import           Data.Typeable               (Typeable)
import           Prelude
import           Test.QuickCheck             (Arbitrary)

import           ZkFold.Base.Data.ByteString (ToByteString(..), FromByteString (..))

type Transcript = ByteString

transcript :: ToByteString a => Transcript -> a -> Transcript
transcript ts a = ts <> toByteString a

challenge :: FromByteString a => Transcript -> (a, Transcript)
challenge ts =
    let bs  = hash ts
        ts' = snoc ts 0
    in (fromJust $ fromByteString bs, ts')

challenges :: FromByteString a => Transcript -> Integer -> ([a], Transcript)
challenges ts0 n = go ts0 n []
  where
    go ts 0 acc = (acc, ts)
    go ts k acc =
        let (c, ts') = challenge ts
        in go ts' (k - 1) (c : acc)

class (Arbitrary (Params a), Arbitrary (SetupSecret a), Arbitrary (ProverSecret a), Arbitrary (Witness a),
       Show (Setup a), Show (ProverSecret a), Show (Witness a), Typeable a)
        => NonInteractiveProof a where
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