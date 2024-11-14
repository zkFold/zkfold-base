{-# LANGUAGE DeriveAnyClass      #-}

module ZkFold.Base.Protocol.Protostar.NARK where

import           Control.DeepSeq                             (NFData (..))
import           Data.Zip                                    (unzip)
import           GHC.Generics
import           Prelude                                     hiding (length, head, unzip, pi)

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
data NARKProof c m k
    = NARKProof
        { narkCommits :: Vector k c -- Commits [C_i] ∈  C^k
        , narkWitness :: Vector k m -- prover messages in the special-sound protocol [m_i]
        }
    deriving (Show, Generic, NFData)

data InstanceProofPair f i c m k = InstanceProofPair (i f) (NARKProof c m k)
    deriving (Show, Generic, NFData)

instanceProof :: forall a f i m k c .
    ( Ring f
    , KnownNat k
    , SpecialSoundProtocol f i m k a
    , HomomorphicCommit m c
    , RandomOracle (i f) f
    , RandomOracle c f
    ) => FiatShamir f (CommitOpen m c a) -> i f -> InstanceProofPair f i c m k
instanceProof a pi =
    let (ms, cs) = unzip $ prover @f @i @(Vector k (m, c)) @1 a pi (oracle pi) 0
    in InstanceProofPair pi (NARKProof cs ms)
