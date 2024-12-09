{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}

module ZkFold.Base.Protocol.IVC.FiatShamir where

import           Data.Constraint                       (withDict)
import           Data.Constraint.Nat                   (plusMinusInverse1)
import           Prelude                               hiding (Bool (..), Eq (..), init, length, pi, scanl, unzip)

import           ZkFold.Base.Algebra.Basic.Number      (KnownNat, type (-))
import           ZkFold.Base.Data.Vector               (Vector, init, item, scanl, unfold)
import           ZkFold.Base.Protocol.IVC.CommitOpen
import           ZkFold.Base.Protocol.IVC.Oracle       (RandomOracle (..))
import           ZkFold.Base.Protocol.IVC.SpecialSound (SpecialSoundProtocol (..))

type FiatShamir d k i p o m c f = SpecialSoundProtocol d 1 i p (Vector k c, o) (Vector k (m, c)) c f

-- The transcript of the Fiat-Shamired protocol (ignoring the last round)
transcriptFiatShamir :: forall algo k c f . RandomOracle algo (f, c) f
    => f -> Vector k c -> Vector (k-1) f
transcriptFiatShamir r0 cs = withDict (plusMinusInverse1 @1 @k) $ init $ init $ scanl (curry (oracle @algo @(f, c))) r0 cs

fiatShamirTransform :: forall algo d k i p o m c f.
    ( KnownNat k
    , RandomOracle algo (i f) f
    , RandomOracle algo (f, c) f
    ) => CommitOpen d k i p o m c f -> FiatShamir d k i p o m c f
fiatShamirTransform SpecialSoundProtocol {..} =
    let
        prover' pi0 w _ _ =
            let r0 = oracle @algo pi0
                f (r, k) =
                    let (m', c') = prover pi0 w r k
                    in ((m', c'), (oracle @algo (r, c'), k + 1))
            in unfold f (r0, 1)

        verifier' pi pms' _ =
            let pms = item pms'
                r0 = oracle @algo pi :: f
                rs = transcriptFiatShamir @algo r0 $ fmap snd pms
            in verifier pi pms rs
    in
        SpecialSoundProtocol input prover' verifier'