{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant ^." #-}

module ZkFold.Base.Protocol.Protostar.AccumulatorScheme where

import           Control.Lens                                ((^.))
import           Data.List                                   (transpose)
import qualified Data.Vector                                 as DV
import           Prelude                                     (type (~), ($), (.), (<$>), concatMap)
import qualified Prelude                                     as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Algebra.Polynomials.Univariate  as PU
import           ZkFold.Base.Protocol.Protostar.Accumulator
import           ZkFold.Base.Protocol.Protostar.Commit       (HomomorphicCommit (..))
import           ZkFold.Base.Protocol.Protostar.CommitOpen   (CommitOpen (..), CommitOpenProverMessage (..))
import           ZkFold.Base.Protocol.Protostar.FiatShamir   (FiatShamir (..))
import           ZkFold.Base.Protocol.Protostar.Oracle       (RandomOracle (..))
import           ZkFold.Base.Protocol.Protostar.SpecialSound (AlgebraicMap (..), MapInput, SpecialSoundProtocol (..))
import           ZkFold.Symbolic.Data.Class                  (SymbolicData(..))
import ZkFold.Base.Data.Vector (Vector, fromVector)

-- | Accumulator scheme for V_NARK as described in Chapter 3.4 of the Protostar paper
--
class AccumulatorScheme pi f c m a where
  prover   :: a
           -> f                           -- Commitment key ck
           -> Accumulator pi f c m        -- accumulator
           -> InstanceProofPair pi c m    -- instance-proof pair (pi, π)
           -> (Accumulator pi f c m, [c]) -- updated accumulator and accumulation proof

  verifier :: pi                          -- Public input
           -> [c]                         -- NARK proof π.x
           -> AccumulatorInstance pi f c  -- accumulator instance acc.x
           -> AccumulatorInstance pi f c  -- updated accumulator instance acc'.x
           -> [c]                         -- accumulation proof E_j
           -> (f, pi, [f], [c], c)        -- returns zeros if the accumulation proof is correct

  decider  :: a
           -> f                           -- Commitment key ck
           -> Accumulator pi f c m        -- final accumulator
           -> ([c], c)                    -- returns zeros if the final accumulator is valid

type SymbolicDataRepresentableAsVector n f x = (SymbolicData x, Support x ~ (), Context x (Layout x) ~ Vector n f)

pieces' :: SymbolicDataRepresentableAsVector n f x => x -> [f]
pieces' = fromVector . (`pieces` ())

instance
    ( AdditiveGroup pi
    , AdditiveGroup c
    , AdditiveSemigroup m
    , Ring f
    , Scale f pi
    , Scale f c
    , Scale f m
    , RandomOracle pi f         -- Random oracle for compressing public input
    , RandomOracle c f          -- Random oracle ρ_NARK
    , HomomorphicCommit f [f] c
    , HomomorphicCommit f m c
    , SymbolicDataRepresentableAsVector n f pi
    , SymbolicDataRepresentableAsVector n f m
    , AlgebraicMap f (CommitOpen m c a)
    , MapInput f a ~ pi
    , MapMessage f a ~ m
    , Degree (FiatShamir f (CommitOpen m c a)) + 1 ~ deg
    , KnownNat deg
    , AlgebraicMap (PU.PolyVec f deg) a
    , MapInput (PU.PolyVec f deg) a ~ [PU.PolyVec f deg]
    , MapMessage (PU.PolyVec f deg) a ~ PU.PolyVec f deg
    ) => AccumulatorScheme pi f c m (FiatShamir f (CommitOpen m c a)) where
  prover (FiatShamir (CommitOpen _ sps)) ck acc (InstanceProofPair pubi (NARKProof pi_x pi_w)) =
        (Accumulator (AccumulatorInstance pi'' ci'' ri'' eCapital' mu') m_i'', pf)
      where
          -- Fig. 3, step 1
          r_i :: [f]
          r_i = P.scanl (P.curry oracle) (oracle pubi) pi_x

          -- Fig. 3, step 2

          -- X + mu as a univariate polynomial
          polyMu :: PU.PolyVec f deg
          polyMu = PU.polyVecLinear one (acc^.x^.mu)

          -- X * pi + pi' as a list of univariate polynomials
          polyPi :: [PU.PolyVec f deg]
          polyPi = P.zipWith (PU.polyVecLinear @f) (pieces' pubi) (pieces' (acc^.x^.pi))

          -- X * mi + mi'
          polyW :: [PU.PolyVec f deg]
          polyW = P.zipWith (PU.polyVecLinear @f) (concatMap pieces' pi_w) (concatMap pieces' (acc^.w))

          -- X * ri + ri'
          polyR :: [PU.PolyVec f deg]
          polyR = P.zipWith (P.flip PU.polyVecLinear) (acc^.x^.r) r_i

          -- The @l x d+1@ matrix of coefficients as a vector of @l@ univariate degree-@d@ polynomials
          --
          e_uni :: [PU.PolyVec f deg]
          e_uni = algebraicMap @(PU.PolyVec f deg) sps polyPi polyW polyR polyMu

          -- e_all are coefficients of degree-j homogenous polynomials where j is from the range [0, d]
          e_all = transpose $ DV.toList . PU.fromPolyVec <$> e_uni

          -- e_j are coefficients of degree-j homogenous polynomials where j is from the range [1, d - 1]
          e_j :: [[f]]
          e_j = P.tail . P.init $ e_all

          -- Fig. 3, step 3
          pf = hcommit ck <$> e_j

          -- Fig. 3, step 4
          alpha :: f
          alpha = oracle (acc^.x, pubi, pi_x, pf)

          -- Fig. 3, steps 5, 6
          mu'   = alpha + acc^.x^.mu
          pi''  = scale alpha pubi + acc^.x^.pi
          ri''  = scale alpha r_i  + acc^.x^.r
          ci''  = scale alpha pi_x + acc^.x^.c
          m_i'' = scale alpha pi_w + acc^.w

          -- Fig. 3, step 7
          eCapital' = acc^.x^.e + sum (P.zipWith (\e' p -> scale (alpha ^ p) e') pf [1::Natural ..])


  verifier pubi c_i acc acc' pf = (muDiff, piDiff, riDiff, ciDiff, eDiff)
      where
          -- Fig. 4, step 1
          r_i :: [f]
          r_i = P.scanl (P.curry oracle) (oracle pubi) c_i

          -- Fig. 4, step 2
          alpha :: f
          alpha = oracle (acc, pubi, c_i, pf)

          -- Fig. 4, step 3
          mu'  = alpha + acc^.mu
          pi'' = scale alpha pubi + acc^.pi
          ri'' = scale alpha r_i  + acc^.r
          ci'' = scale alpha c_i  + acc^.c

          -- Fig 4, step 4
          muDiff = acc'^.mu - mu'
          piDiff = acc'^.pi - pi''
          riDiff = acc'^.r  - ri''
          ciDiff = acc'^.c  - ci''

          -- Fig 4, step 5
          eDiff = acc'^.e - (acc^.e + sum (P.zipWith scale ((alpha ^) <$> [1 :: Natural ..]) pf))

  decider (FiatShamir sps) ck acc = (commitsDiff, eDiff)
      where
          -- Fig. 5, step 1
          commitsDiff = P.zipWith (\cm m_acc -> cm - hcommit ck m_acc) (acc^.x^.c) (acc^.w)

          -- Fig. 5, step 2
          err :: [f]
          err = algebraicMap @f sps (acc^.x^.pi) [Open $ acc^.w] (acc^.x^.r) (acc^.x^.mu)


          -- Fig. 5, step 3
          eDiff = (acc^.x^.e) - hcommit ck err
