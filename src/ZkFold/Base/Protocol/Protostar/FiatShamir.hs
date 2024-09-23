{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.FiatShamir where

import           Data.ByteString                             (ByteString)
import           GHC.Generics
import           Prelude                                     hiding (Bool (..), Eq (..), length)
import qualified Prelude                                     as P

import           ZkFold.Base.Data.ByteString                 (Binary (..))
import           ZkFold.Base.Protocol.NonInteractiveProof    (NonInteractiveProof (..), ToTranscript (..), challenge)
import           ZkFold.Base.Protocol.Protostar.CommitOpen
import qualified ZkFold.Base.Protocol.Protostar.SpecialSound as SpS
import           ZkFold.Base.Protocol.Protostar.SpecialSound (SpecialSoundProtocol (..), SpecialSoundTranscript)
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Eq

data FiatShamir f a = FiatShamir a (SpS.Input f a)
    deriving Generic

fsChallenge
    :: forall f a c m
    .  Binary (SpS.Input f a)
    => Binary (VerifierMessage f a)
    => Binary c
    => Binary (ProverMessage f a)
    => m ~ ProverMessage f a
    => FiatShamir f (CommitOpen m c a)
    -> SpecialSoundTranscript f (CommitOpen m c a) -> ProverMessage f (CommitOpen m c a) -> VerifierMessage f a
fsChallenge (FiatShamir _ ip) []           c =
      let r0 = challenge @ByteString $ toTranscript ip :: VerifierMessage f a
      in challenge @ByteString $ toTranscript r0 <> toTranscript c
fsChallenge _                 ((_, r) : _) c = challenge @ByteString $ toTranscript r <> toTranscript c

instance
    ( SpS.SpecialSoundProtocol f a
    , Binary (SpS.Input f a)
    , Binary (VerifierMessage f a)
    , VerifierMessage f a ~ f
    , ProverMessage f a ~ m
    , Binary c
    , Binary (ProverMessage f a)
    , BoolType (VerifierOutput f a)
    , Eq (VerifierOutput f a) [c]
    , VerifierOutput f a ~ P.Bool
    ) => NonInteractiveProof (FiatShamir f (CommitOpen m c a)) core where
      type Transcript (FiatShamir f (CommitOpen m c a))  = ByteString
      type SetupProve (FiatShamir f (CommitOpen m c a))  = FiatShamir f (CommitOpen m c a)
      type SetupVerify (FiatShamir f (CommitOpen m c a)) = FiatShamir f (CommitOpen m c a)
      type Witness (FiatShamir f (CommitOpen m c a))     = SpS.Witness f a
      type Input (FiatShamir f (CommitOpen m c a))       = (SpS.Input f a, [c])
      type Proof (FiatShamir f (CommitOpen m c a))       = [ProverMessage f a]

      setupProve x = x

      setupVerify x = x

      prove fs@(FiatShamir a ip) w =
            let (ms, ts) = opening @f @a @c @m a w ip (fsChallenge fs)
            in ((ip, commits @f @a @c @m ts), ms)

      verify fs@(FiatShamir a _) (ip, cs) ms =
            let ts' = foldl (\acc c -> acc ++ [(c, fsChallenge fs acc c)]) [] $ map Commit cs
                ts  = ts' ++ [(Open ms, fsChallenge fs ts' $ Open ms)]
                (ri, ci) = unzip ts
            in verifier a ip ri ci

