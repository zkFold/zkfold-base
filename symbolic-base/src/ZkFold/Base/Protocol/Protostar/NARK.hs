{-# LANGUAGE DeriveAnyClass      #-}

module ZkFold.Base.Protocol.Protostar.NARK where

import           Control.DeepSeq                             (NFData (..))
import           Data.Zip                                    (unzip)
import           GHC.Generics
import           Prelude                                     hiding (length, head, unzip, pi)

import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Base.Protocol.Protostar.Commit       (HomomorphicCommit)
import           ZkFold.Base.Protocol.Protostar.CommitOpen   (CommitOpen (..))
import           ZkFold.Base.Protocol.Protostar.FiatShamir   (FiatShamir)
import           ZkFold.Base.Protocol.Protostar.Oracle       (RandomOracle (..))
import           ZkFold.Base.Protocol.Protostar.SpecialSound (BasicSpecialSoundProtocol, SpecialSoundProtocol (..))

-- Page 18, section 3.4, The accumulation predicate
--
data NARKProof c m k
    = NARKProof
        { narkCommits :: Vector k c -- Commits [C_i] ∈  C^k
        , narkWitness :: Vector k m -- prover messages in the special-sound protocol [m_i]
        }
    deriving (Show, Generic, NFData)

data InstanceProofPair pi c m k = InstanceProofPair pi (NARKProof c m k)
    deriving (Show, Generic, NFData)

instanceProof :: forall a f pi m k c .
    ( BasicSpecialSoundProtocol f pi m k a
    , RandomOracle pi f
    , RandomOracle (f, c) f
    , HomomorphicCommit m c
    ) => FiatShamir f (CommitOpen m c a) -> pi -> InstanceProofPair pi c m k
instanceProof a pi =
    let (ms, cs) = unzip $ prover @f @pi @(Vector k (m, c)) @1 a pi (oracle pi) 0
    in InstanceProofPair pi (NARKProof cs ms)

{--
toAccumulatorInstance :: (FiniteField f, AdditiveGroup c) => (f -> c -> f) -> NARKInstance f c -> AccumulatorInstance f c
toAccumulatorInstance oracle (NARKInstance i cs) =
      let r0 = oracle i zero
          f acc@(r:_) c = oracle r c : acc
          f []        _ = error "Invalid accumulator instance"
          rs = init $ reverse $ foldl f [r0] cs
      in AccumulatorInstance i cs rs zero one

toAccumulatorWitness :: NARKWitness m -> AccumulatorWitness m
toAccumulatorWitness (NARKWitness ms) = AccumulatorWitness ms

toAccumulator :: (FiniteField f, AdditiveGroup c) => (f -> c -> f) -> NARKPair pi f c m -> Accumulator f c m
toAccumulator oracle (NARKPair i w) = Accumulator (toAccumulatorInstance oracle i) (toAccumulatorWitness w)
--}
