module ZkFold.Base.Protocol.IVC.NARK where

import           Data.Zip                            (unzip)
import           GHC.Generics
import           Prelude                             hiding (head, length, pi, unzip)

import           ZkFold.Base.Data.Vector             (Vector)
import           ZkFold.Base.Protocol.IVC.Commit     (HomomorphicCommit)
import           ZkFold.Base.Protocol.IVC.FiatShamir (FiatShamir (..))
import           ZkFold.Base.Protocol.IVC.Predicate  (PredicateFunctionAssumptions)
import           ZkFold.Symbolic.MonadCircuit        (ResidueField)

-- Page 18, section 3.4, The accumulation predicate
--
data NARKProof k c f
    = NARKProof
        { narkCommits :: Vector k (c f) -- Commits [C_i] ∈  C^k
        , narkWitness :: Vector k [f]   -- prover messages in the special-sound protocol [m_i]
        }
    deriving (Generic)

narkProof :: forall k a i p c f . (PredicateFunctionAssumptions a f, ResidueField f, HomomorphicCommit [f] (c f))
    => FiatShamir k a i p c
    -> i f
    -> p f
    -> NARKProof k c f
narkProof FiatShamir {..} pi0 w =
    let (narkWitness, narkCommits) = unzip $ prover pi0 w
    in NARKProof {..}

data NARKInstanceProof k i c f = NARKInstanceProof (i f) (NARKProof k c f)
    deriving (Generic)

narkInstanceProof :: forall k a i p c f . (PredicateFunctionAssumptions a f, ResidueField f, HomomorphicCommit [f] (c f))
    => FiatShamir k a i p c
    -> i f
    -> p f
    -> NARKInstanceProof k i c f
narkInstanceProof fs@FiatShamir {..} pi0 w = NARKInstanceProof (input pi0 w) (narkProof fs pi0 w)
