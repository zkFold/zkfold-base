{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.IVC.FiatShamir where

import           Data.Constraint                       (withDict)
import           Data.Constraint.Nat                   (plusMinusInverse1)
import           GHC.Generics                          (Generic)
import           Prelude                               hiding (Bool (..), Eq (..), init, length, pi, scanl, unzip)

import           ZkFold.Base.Algebra.Basic.Number      (KnownNat, type (-))
import           ZkFold.Base.Data.Vector               (Vector, init, item, scanl, unfold)
import           ZkFold.Base.Protocol.IVC.Commit       (HomomorphicCommit)
import           ZkFold.Base.Protocol.IVC.CommitOpen
import           ZkFold.Base.Protocol.IVC.Oracle       (RandomOracle (..), HashAlgorithm)
import           ZkFold.Base.Protocol.IVC.SpecialSound (SpecialSoundProtocol (..))

newtype FiatShamir algo a = FiatShamir a
    deriving Generic

-- The transcript of the Fiat-Shamired protocol (ignoring the last round)
transcriptFiatShamir :: forall algo f c k . (RandomOracle algo (f, c) f) => f -> Vector k c -> Vector (k-1) f
transcriptFiatShamir r0 cs = withDict (plusMinusInverse1 @1 @k) $ init $ init $ scanl (curry (oracle @algo @(f, c))) r0 cs

instance
    ( SpecialSoundProtocol f i p m c d k a
    , HashAlgorithm algo f
    , HomomorphicCommit m c
    , RandomOracle algo (i f) f
    , RandomOracle algo c f
    , KnownNat k
    ) => SpecialSoundProtocol f i p (Vector k (m, c)) c d 1 (FiatShamir algo (CommitOpen a)) where
        type VerifierOutput f i p (Vector k (m, c)) c d 1 (FiatShamir algo (CommitOpen a)) = VerifierOutput f i p (m, c) c d k (CommitOpen a)

        input (FiatShamir a) = input @_ @_ @_ @(m, c) @c @d @k a

        prover (FiatShamir a) pi0 w _ _ =
            let r0 = oracle @algo pi0
                f (r, k) =
                    let (m', c') = prover @f @i @_ @(m, c) @c @d @k a pi0 w r k
                    in ((m', c'), (oracle @algo (r, c'), k + 1))
            in unfold f (r0, 1)

        verifier (FiatShamir a) pi pms' _ =
            let pms = item pms'
                r0 = oracle @algo pi :: f
                rs = transcriptFiatShamir @algo r0 $ fmap snd pms
            in verifier @f @i @p @(m, c) @c @d @k a pi pms rs
