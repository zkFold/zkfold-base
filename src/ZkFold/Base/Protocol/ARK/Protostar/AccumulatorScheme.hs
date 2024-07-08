{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.ARK.Protostar.AccumulatorScheme where

import           Control.Lens                                    ((^.))
import           Prelude                                         hiding (length)

import           ZkFold.Base.Protocol.ARK.Protostar.Accumulator
import           ZkFold.Base.Protocol.ARK.Protostar.CommitOpen   (CommitOpen (..))
import           ZkFold.Base.Protocol.ARK.Protostar.FiatShamir   (FiatShamir (..), fsChallenge)
import           ZkFold.Base.Protocol.ARK.Protostar.Oracle       (RandomOracle (..))
import           ZkFold.Base.Protocol.ARK.Protostar.SpecialSound (Input, ProverMessage)


-- | Accumulator scheme for V_NARK as described in Chapter 3.4 of the Protostar paper
--
class AccumulatorScheme f c m a where
  commit   :: a -> m -> c

  prover   :: a                        -- input commitment key
           -> Accumulator f c m        -- accumulator
           -> InstanceProofPair f c m  -- instance-proof pair (pi, π)
           -> (Accumulator f c m, [f]) -- updated accumulator and accumulation proof

  verifier :: f                        -- Public input
           -> [c]                      -- NARK proof π.x
           -> AccumulatorInstance f c  -- accumulator instance acc.x
           -> AccumulatorInstance f c  -- updated accumulator instance acc'.x
           -> [c]                      -- accumulation proof E_j
           -> Bool

  decider  :: a                   -- Commitment key ck
           -> Accumulator f c m   -- accumulator
           -> Bool

instance
    ( Input f a ~ f
    , ProverMessage f a ~ m
    , RandomOracle (f, c) f                                  -- Random oracle ρ_NARK
    , RandomOracle (AccumulatorInstance f c, f, [c], [c]) f  -- Random oracle ρ_acc
    ) => AccumulatorScheme f c m (FiatShamir f (CommitOpen f c a)) where
  commit (FiatShamir (CommitOpen cm _) _) = cm

-- TODO: pages 20-21
--
  prover (FiatShamir (CommitOpen cm a) _) acc (InstanceProofPair pi (NARKProof pi_x pi_w)) =
      (Accumulator (AccumulatorInstance pi'' ci'' ri'' eCapital' mu') (AccumulatorWitness mi''), eCapital_j)
      where
          -- Fig. 3, step 1
          r_i = tail $ scanl (uncurry $ flip oracle) zero (pi : pi_x)

          -- Fig. 3, step 2
          e_j = undefined

          -- Fig. 3, step 3
          eCapital_j = undefined

          -- Fig. 3, step 4
          alpha = oracle (acc^.x, pi, pi_x, eCapital_j)

          -- Fig. 3, steps 5, 6
          mu'  = alpha      + acc^.x^.mu
          pi'' = alpha * pi + acc^.x^.pi
          ri'' = zipWith (\r r' -> alpha * r + r') ri   $ acc^.x^.r
          ci'' = zipWith (\c c' -> alpha * c + c') pi_x $ acc^.x^.c
          mi'' = zipWith (\m m' -> alpha * m + m') pi_w $ acc^.w

          -- Fig. 3, step 7
          eCapital' = undefined


  verifier pi c_i acc acc' pf = and [muEq, piEq, riEq, ciEq, eEq]
      where
          -- Fig. 4, step 1
          r_i = tail $ scanl (uncurry $ flip oracle) zero (pi : c_i)

          -- Fig. 4, step 2
          alpha = oracle (acc^.x, pi, c_i, pf)

          -- Fig. 4, step 3
          mu'  = alpha      + acc^.x^.mu
          pi'' = alpha * pi + acc^.x^.pi
          ri'' = zipWith (\r r' -> alpha * r + r') ri   $ acc^.x^.r
          ci'' = zipWith (\c c' -> alpha * c + c') pi_x $ acc^.x^.c

          -- Fig 4, step 4
          muEq = acc'^.x^.mu == mu'
          piEq = acc'^.x^.pi == pi''
          riEq = acc'^.x^.r  == ri''
          ciEq = acc'^.x^.c  == ci''

          -- Fig 4, step 5
          eEq = acc'^.x^.e == acc^.x^.e + sum (zipWith (*) pf (iterate (\x -> x * x) alpha))

  decider (FiatShamir (CommitOpen cm a) _) acc = commitsEq && eEq
      where
          -- Fig. 5, step 1
          commitsEq = and $ zipWith (\c m -> cm m == c) (acc^.x^.c) (acc^.w)

          -- Fig. 5, step 2
          err = undefined

          -- Fig. 5, step 3
          eEq = acc^.x^.e == cm err

