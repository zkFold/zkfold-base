{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Base.Protocol.NonInteractiveProof where

import           Control.DeepSeq             (NFData)
import           Crypto.Hash.SHA256          (hash)
import           Data.Aeson
import           Data.ByteString             (ByteString, cons)
import qualified Data.ByteString.Base64      as B64
import qualified Data.ByteString.Char8       as BS
import           Data.Maybe                  (fromJust)
import qualified Data.Text                   as T
import           GHC.Generics                (Generic)
import           Numeric.Natural             (Natural)
import           Prelude
import           Test.QuickCheck             (Arbitrary (..), generate, vectorOf)

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

    type SetupProve a

    type SetupVerify a

    type Witness a

    type Input a

    type Proof a

    setupProve :: a -> SetupProve a

    setupVerify :: a -> SetupVerify a

    prove :: SetupProve a -> Witness a -> (Input a, Proof a)

    verify :: SetupVerify a -> Input a -> Proof a -> Bool

newtype ProofBytes = ProofBytes
  { fromWitnessBytes :: ByteString }
  deriving (Show, Eq, Generic, NFData)

instance ToJSON ProofBytes where
    toJSON (ProofBytes b) = String . T.pack . BS.unpack . B64.encode $ b

instance FromJSON ProofBytes where
    parseJSON = withText "Bytes of proof" $ \t ->
        case B64.decode . BS.pack . T.unpack $ t of
            Left err -> fail err
            Right bs -> return $ ProofBytes bs

data ProveAPIResult = ProveAPISuccess ProofBytes | ProveAPIErrorSetup | ProveAPIErrorWitness
    deriving (Show, Eq, Generic, NFData)

proveAPI
    :: forall a
    . (NonInteractiveProof a
    , Binary (SetupProve a)
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
        (Just s, Just w) -> ProveAPISuccess . ProofBytes $ toByteString $ prove @a s w

testVector :: forall a .
    NonInteractiveProof a =>
    Arbitrary a =>
    Arbitrary (Witness a) =>
    Binary (SetupProve a) =>
    Binary (Input a) =>
    Binary (Proof a) =>
    Int -> IO [(ByteString, ByteString, ByteString)]
testVector n = generate . vectorOf n $ (,)
    <$> arbitrary @a
    <*> arbitrary @(Witness a)
    >>= \(a, w) -> do
        let s = setupProve @a a
        let (i, p) = prove @a s w
        pure (toByteString s, toByteString i, toByteString p)
