{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Base.Protocol.ARK.Protostar.Accumulator where

import           Prelude                         hiding (length)

import           ZkFold.Base.Algebra.Basic.Class

data AccumulatorInstance f c = AccumulatorInstance
  { accPublicInput :: f,
    accCommits     :: [c],
    accChallenges  :: [f],
    accError       :: c,
    accMu          :: f
  }

newtype AccumulatorWitness m = AccumulatorWitness {accMessages :: [m]}

data Accumulator f c m = Accumulator (AccumulatorInstance f c) (AccumulatorWitness m)

data NARKInstance f c = NARKInstance
  { narkPublicInput :: f,
    narkCommits     :: [c]
  }

newtype NARKWitness m = NARKWitness {narkMessages :: [m]}

data NARKPair pi f c m = NARKPair (NARKInstance f c) (NARKWitness m)

toAccumulatorInstance :: (FiniteField f, AdditiveGroup c) => (f -> c -> f) -> NARKInstance f c -> AccumulatorInstance f c
toAccumulatorInstance oracle (NARKInstance i cs) =
  let r0 = oracle i zero
      f acc@(r : _) c = oracle r c : acc
      f [] _          = error "Invalid accumulator instance"
      rs = init $ reverse $ foldl f [r0] cs
   in AccumulatorInstance i cs rs zero one

toAccumulatorWitness :: NARKWitness m -> AccumulatorWitness m
toAccumulatorWitness (NARKWitness ms) = AccumulatorWitness ms

toAccumulator :: (FiniteField f, AdditiveGroup c) => (f -> c -> f) -> NARKPair pi f c m -> Accumulator f c m
toAccumulator oracle (NARKPair i w) = Accumulator (toAccumulatorInstance oracle i) (toAccumulatorWitness w)
