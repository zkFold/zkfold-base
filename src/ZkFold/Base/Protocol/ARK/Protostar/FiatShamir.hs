{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.ARK.Protostar.FiatShamir where

import           Data.ByteString                                 (ByteString)
import           Prelude                                         hiding (length)

import           ZkFold.Base.Data.ByteString                     (ToByteString (..), FromByteString)
import           ZkFold.Base.Protocol.ARK.Protostar.CommitOpen
import           ZkFold.Base.Protocol.ARK.Protostar.SpecialSound (SpecialSoundProtocol(..), SpecialSoundTranscript)
import qualified ZkFold.Base.Protocol.ARK.Protostar.SpecialSound as SpS
import           ZkFold.Base.Protocol.NonInteractiveProof        (NonInteractiveProof(..), ToTranscript (..), challenge)

data FiatShamir a = FiatShamir a (SpS.Input a)

fsChallenge :: forall a c . (ToByteString (SpS.Input a), FromByteString (VerifierMessage a),
      ToByteString c, ToByteString (VerifierMessage a)) => FiatShamir (CommitOpen c a)
      -> SpecialSoundTranscript (CommitOpen c a) -> ProverMessage (CommitOpen c a) -> VerifierMessage a
fsChallenge (FiatShamir _ ip) []           c =
      let r0 = fst $ challenge @ByteString $ toTranscript ip :: VerifierMessage a
      in fst $ challenge @ByteString $ toTranscript r0 <> toTranscript c
fsChallenge _                 ((_, r) : _) c = fst $ challenge @ByteString $ toTranscript r <> toTranscript c

instance (SpS.SpecialSoundProtocol a, Eq c, ToByteString (SpS.Input a), FromByteString (VerifierMessage a),
            ToByteString c, ToByteString (VerifierMessage a)) => NonInteractiveProof (FiatShamir (CommitOpen c a)) where
      type Transcript (FiatShamir (CommitOpen c a)) = ByteString
      type Setup (FiatShamir (CommitOpen c a))      = FiatShamir (CommitOpen c a)
      type Witness (FiatShamir (CommitOpen c a))    = SpS.Witness a
      type Input (FiatShamir (CommitOpen c a))      = (SpS.Input a, [c])
      type Proof (FiatShamir (CommitOpen c a))      = [ProverMessage a]

      setup x = x

      prove fs@(FiatShamir a ip) w =
            let (ms, ts) = opening a w ip (fsChallenge fs)
            in ((ip, commits ts), ms)
      
      verify fs@(FiatShamir a _) (ip, cs) ms =
            let ts' = foldl (\acc c -> acc ++ [(c, fsChallenge fs acc c)]) [] $ map Commit cs
                ts  = ts' ++ [(Open ms, fsChallenge fs ts' $ Open ms)]
            in verifier a ip ts