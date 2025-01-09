module ZkFold.Base.Protocol.IVC.NARK where

import           Data.Zip                              (unzip)
import           GHC.Generics
import           Prelude                               hiding (head, length, pi, unzip)

import           ZkFold.Base.Data.Vector               (Vector)
import           ZkFold.Base.Protocol.IVC.FiatShamir   (FiatShamir (..))
import           ZkFold.Symbolic.Class                 (Symbolic(..))

-- Page 18, section 3.4, The accumulation predicate
--
data NARKProof k c ctx
    = NARKProof
        { narkCommits :: Vector k (c (WitnessField ctx)) -- Commits [C_i] ∈  C^k
        , narkWitness :: Vector k [WitnessField ctx]     -- prover messages in the special-sound protocol [m_i]
        }
    deriving (Generic)

narkProof ::
       FiatShamir k i p c ctx
    -> i (WitnessField ctx)
    -> p (WitnessField ctx)
    -> NARKProof k c ctx
narkProof FiatShamir {..} pi0 w =
    let (narkWitness, narkCommits) = unzip $ prover pi0 w
    in NARKProof {..}

data NARKInstanceProof k i c ctx = NARKInstanceProof (i (WitnessField ctx)) (NARKProof k c ctx)
    deriving (Generic)

narkInstanceProof ::
       FiatShamir k i p c ctx
    -> i (WitnessField ctx)
    -> p (WitnessField ctx)
    -> NARKInstanceProof k i c ctx
narkInstanceProof fs@FiatShamir {..} pi0 w = NARKInstanceProof (input pi0 w) (narkProof fs pi0 w)
