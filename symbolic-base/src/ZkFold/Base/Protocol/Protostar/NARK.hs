{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveAnyClass      #-}

module ZkFold.Base.Protocol.Protostar.NARK where

import           Control.DeepSeq                             (NFData (..))
import           Data.Zip                                    (unzip)
import           GHC.Generics
import           Prelude                                     hiding (head, length, pi, unzip)

import           ZkFold.Base.Algebra.Basic.Class             (Ring)
import           ZkFold.Base.Algebra.Basic.Number            (KnownNat)
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Base.Protocol.Protostar.Commit       (HomomorphicCommit)
import           ZkFold.Base.Protocol.Protostar.CommitOpen   (CommitOpen (..))
import           ZkFold.Base.Protocol.Protostar.FiatShamir   (FiatShamir)
import           ZkFold.Base.Protocol.Protostar.Oracle       (RandomOracle (..))
import           ZkFold.Base.Protocol.Protostar.SpecialSound (SpecialSoundProtocol (..))

-- Page 18, section 3.4, The accumulation predicate
--
data NARKProof m c k
    = NARKProof
        { narkCommits :: Vector k c -- Commits [C_i] ∈  C^k
        , narkWitness :: Vector k m -- prover messages in the special-sound protocol [m_i]
        }
    deriving (Show, Generic, NFData)

narkProof :: forall f i p m c d k a .
    ( SpecialSoundProtocol f i p m c d k a
    , Ring f
    , HomomorphicCommit m c
    , RandomOracle (i f) f
    , RandomOracle c f
    , KnownNat k
    ) => FiatShamir (CommitOpen a) -> i f -> p f -> NARKProof m c k
narkProof a pi0 w =
    let (ms, cs) = unzip $ prover @f @i @_ @_ @c @d @1 a pi0 w (oracle pi0) 0
    in NARKProof cs ms

data NARKInstanceProof f i m c k = NARKInstanceProof (i f) (NARKProof m c k)
    deriving (Show, Generic, NFData)

narkInstanceProof :: forall f i p m c d k a .
    ( SpecialSoundProtocol f i p m c d k a
    , Ring f
    , HomomorphicCommit m c
    , RandomOracle (i f) f
    , RandomOracle c f
    , KnownNat k
    ) => FiatShamir (CommitOpen a) -> i f -> p f -> NARKInstanceProof f i m c k
narkInstanceProof a pi0 w = NARKInstanceProof (input @f @i @p @(Vector k (m, c)) @c @d @1 a pi0 w) (narkProof @_ @_ @_ @_ @_ @d a pi0 w)
