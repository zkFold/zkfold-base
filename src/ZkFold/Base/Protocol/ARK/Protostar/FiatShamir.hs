{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.ARK.Protostar.FiatShamir where

import           Data.ByteString                                 (ByteString)
import           Prelude                                         hiding (length)

import           ZkFold.Base.Data.ByteString                     (Binary (..))
import           ZkFold.Base.Protocol.ARK.Protostar.CommitOpen
import qualified ZkFold.Base.Protocol.ARK.Protostar.SpecialSound as SpS
import           ZkFold.Base.Protocol.ARK.Protostar.SpecialSound (SpecialSoundProtocol (..), SpecialSoundTranscript)
import           ZkFold.Base.Protocol.NonInteractiveProof        (NonInteractiveProof (..), ToTranscript (..),
                                                                  challenge)

data FiatShamir f a = FiatShamir a (SpS.Input f a)

fsChallenge :: forall f a c . (Binary (SpS.Input f a), Binary (VerifierMessage f a))
      => FiatShamir f (CommitOpen f c a)
      -> SpecialSoundTranscript f (CommitOpen f c a) -> ProverMessage f (CommitOpen f c a) -> VerifierMessage f a
fsChallenge (FiatShamir _ ip) []           c =
      let r0 = fst $ challenge @ByteString $ toTranscript ip :: VerifierMessage f a
      in fst $ challenge @ByteString $ toTranscript r0 <> toTranscript c
fsChallenge _                 ((_, r) : _) c = fst $ challenge @ByteString $ toTranscript r <> toTranscript c

instance (SpS.SpecialSoundProtocol f a, Eq c, Binary (SpS.Input f a), Binary (VerifierMessage f a),
            Binary c, Binary (VerifierMessage f a)) => NonInteractiveProof (FiatShamir f (CommitOpen f c a)) where
      type Transcript (FiatShamir f (CommitOpen f c a)) = ByteString
      type Setup (FiatShamir f (CommitOpen f c a))      = FiatShamir f (CommitOpen f c a)
      type Witness (FiatShamir f (CommitOpen f c a))    = SpS.Witness f a
      type Input (FiatShamir f (CommitOpen f c a))      = (SpS.Input f a, [c])
      type Proof (FiatShamir f (CommitOpen f c a))      = [ProverMessage f a]

      setup x = x

      prove fs@(FiatShamir a ip) w =
            let (ms, ts) = opening a w ip (fsChallenge fs)
            in ((ip, commits ts), ms)

      verify fs@(FiatShamir a _) (ip, cs) ms =
            let ts' = foldl (\acc c -> acc ++ [(c, fsChallenge fs acc c)]) [] $ map Commit cs
                ts  = ts' ++ [(Open ms, fsChallenge fs ts' $ Open ms)]
            in verifier a ip ts
