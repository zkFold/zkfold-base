{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.Protostar.NARK where

import           Control.DeepSeq                             (NFData (..))
import           GHC.Generics
import           Prelude                                     hiding (length, pi)

import           ZkFold.Base.Protocol.Protostar.Commit       (HomomorphicCommit)
import           ZkFold.Base.Protocol.Protostar.CommitOpen   (CommitOpen (..))
import           ZkFold.Base.Protocol.Protostar.FiatShamir   (FiatShamir)
import           ZkFold.Base.Protocol.Protostar.Oracle       (RandomOracle (..))
import           ZkFold.Base.Protocol.Protostar.SpecialSound (SpecialSoundProtocol (..))

-- Page 18, section 3.4, The accumulation predicate
--
data NARKProof c m
    = NARKProof
        { narkCommits :: [c] -- Commits [C_i] ∈  C^k
        , narkWitness :: [m] -- prover messages in the special-sound protocol [m_i]
        }
    deriving (Show, Generic, NFData)

data InstanceProofPair pi c m = InstanceProofPair pi (NARKProof c m)
    deriving (Show, Generic, NFData)

instanceProof :: forall a f pi c m .
    ( RandomOracle pi f
    , RandomOracle (f, c) f
    , HomomorphicCommit m c
    , SpecialSoundProtocol f a
    , Witness f a ~ ()
    , Input f a ~ pi
    , ProverMessage f a ~ m
    , VerifierMessage f a ~ f
    ) => FiatShamir f (CommitOpen m c a) -> pi -> InstanceProofPair pi c m
instanceProof a pi =
    let (c, m) = head $ prover @f a () pi () 0
    in InstanceProofPair pi (NARKProof [c] [m])

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
