{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.FiatShamir where

import           Data.Constraint                             (withDict)
import           Data.Constraint.Nat                         (plusMinusInverse1)
import           GHC.Generics                                (Generic)
import           Prelude                                     hiding (Bool (..), Eq (..), init, length, pi, scanl, unzip)

import           ZkFold.Base.Algebra.Basic.Class             (Ring)
import           ZkFold.Base.Algebra.Basic.Number            (KnownNat, type (-))
import           ZkFold.Base.Data.Vector                     (Vector, init, item, scanl, unfold)
import           ZkFold.Base.Protocol.Protostar.Commit       (HomomorphicCommit)
import           ZkFold.Base.Protocol.Protostar.CommitOpen
import           ZkFold.Base.Protocol.Protostar.Oracle       (RandomOracle (..))
import           ZkFold.Base.Protocol.Protostar.SpecialSound (SpecialSoundProtocol (..))

newtype FiatShamir a = FiatShamir a
    deriving Generic

-- The transcript of the Fiat-Shamired protocol (ignoring the last round)
transcriptFiatShamir :: forall k c f . (Ring f, RandomOracle f f, RandomOracle c f) => f -> Vector k c -> Vector (k-1) f
transcriptFiatShamir r0 cs = withDict (plusMinusInverse1 @1 @k) $ init $ init $ scanl (curry (oracle @(f, c))) r0 cs

instance
    ( SpecialSoundProtocol f i p m c d k a
    , Ring f
    , HomomorphicCommit m c
    , RandomOracle (i f) f
    , RandomOracle c f
    , KnownNat k
    ) => SpecialSoundProtocol f i p (Vector k (m, c)) c d 1 (FiatShamir (CommitOpen a)) where
        type VerifierOutput f i p (Vector k (m, c)) c d 1 (FiatShamir (CommitOpen a)) = VerifierOutput f i p (m, c) c d k (CommitOpen a)

        input (FiatShamir a) = input @_ @_ @_ @(m, c) @c @d @k a

        prover (FiatShamir a) pi0 w _ _ =
            let r0 = oracle pi0
                f (r, k) =
                    let (m', c') = prover @f @i @_ @(m, c) @c @d @k a pi0 w r k
                    in ((m', c'), (oracle (r, c'), k + 1))
            in unfold f (r0, 1)

        verifier (FiatShamir a) pi pms' _ =
            let pms = item pms'
                r0 = oracle pi :: f
                rs = transcriptFiatShamir r0 $ fmap snd pms
            in verifier @f @i @p @(m, c) @c @d @k a pi pms rs
