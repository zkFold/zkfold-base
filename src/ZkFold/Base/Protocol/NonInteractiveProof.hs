{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Base.Protocol.NonInteractiveProof where

import           Control.DeepSeq             (NFData)
import           Crypto.Hash.SHA256          (hash)
import           Data.ByteString             (ByteString, cons)
import           Data.Maybe                  (fromJust)
import           GHC.Generics                (Generic)
import           Numeric.Natural             (Natural)
import           Test.QuickCheck             (Arbitrary (..), vectorOf, generate)
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

data ProveAPIResult = ProveAPISuccess ByteString | ProveAPIErrorSetup | ProveAPIErrorWitness
    deriving (Show, Eq, Generic, NFData)

proveAPI
    :: forall a
    . (NonInteractiveProof a
    , Binary (Setup a)
    , Binary (Witness a)
    , Binary (Input a)
    , Binary (Proof a))
    => ByteString
    -> ByteString
    -> ProveAPIResult
proveAPI bsS bsW =
    let mS = fromByteString bsS
        mW = fromByteString bsW
    in case (mS, mW) of
        (Nothing, _)     -> ProveAPIErrorSetup
        (_, Nothing)     -> ProveAPIErrorWitness
        (Just s, Just w) -> ProveAPISuccess $ toByteString $ prove @a s w

testVector :: forall a .
    NonInteractiveProof a =>
    Arbitrary a =>
    Arbitrary (Witness a) =>
    IO [(Setup a, Input a, Proof a)]
testVector = generate . vectorOf 10 $ (,)
    <$> arbitrary @a
    <*> arbitrary @(Witness a)
    >>= \(a, w) -> do 
        let s = setup @a a
        let (i, p) = prove @a s w
        pure (s, i, p)