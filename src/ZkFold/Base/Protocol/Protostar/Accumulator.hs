{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TemplateHaskell     #-}

module ZkFold.Base.Protocol.Protostar.Accumulator where

import           Control.Lens.Combinators (makeLenses)
import           Prelude                  hiding (length)

-- Page 19, Accumulator instance
data AccumulatorInstance f c = AccumulatorInstance {
      _pi :: f     -- pi ∈  M^{l_in} in the paper
    , _c  :: [c]   -- [C_i] ∈  C^k in the paper
    , _r  :: [f]   -- [r_i] ∈  F^{k-1} in the paper
    , _e  :: c     -- E ∈  C in the paper
    , _mu :: f     -- μ ∈  F in the paper
}

makeLenses ''AccumulatorInstance

-- Page 19, Accumulator
-- @acc.x@ (accumulator instance) from the paper corresponds to _x
-- @acc.w@ (accumulator witness) from the paper corresponds to _w
data Accumulator f c m
    = Accumulator
        { _x :: AccumulatorInstance f c
        , _w :: [m]
        }

makeLenses ''Accumulator

-- Page 18, section 3.4, The accumulation predicate
--
data NARKProof c m
    = NARKProof
        { narkCommits :: [c] -- Commits [C_i] ∈  C^k
        , narkWitness :: [m] -- prover messages in the special-sound protocol [m_i]
        }

data InstanceProofPair pi c m = InstanceProofPair pi (NARKProof c m)

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
