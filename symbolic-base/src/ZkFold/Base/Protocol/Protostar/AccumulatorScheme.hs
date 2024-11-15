{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant ^." #-}

module ZkFold.Base.Protocol.Protostar.AccumulatorScheme where

import           Control.Lens                                ((^.))
import           Data.List                                   (transpose)
import qualified Data.Vector                                 as DV
import           Data.Zip                                    (Zip (..))
import           GHC.IsList                                  (IsList (..))
import           Prelude                                     (fmap, ($), (.), (<$>))
import qualified Prelude                                     as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Algebra.Polynomials.Univariate  as PU
import           ZkFold.Base.Data.Vector                     (Vector, mapWithIx, unsafeToVector)
import           ZkFold.Base.Protocol.Protostar.Accumulator
import           ZkFold.Base.Protocol.Protostar.AlgebraicMap (AlgebraicMap (..))
import           ZkFold.Base.Protocol.Protostar.Commit       (HomomorphicCommit (..))
import           ZkFold.Base.Protocol.Protostar.CommitOpen   (CommitOpen (..))
import           ZkFold.Base.Protocol.Protostar.FiatShamir   (FiatShamir (..), transcriptFiatShamir)
import           ZkFold.Base.Protocol.Protostar.NARK         (InstanceProofPair (..), NARKProof (..))
import           ZkFold.Base.Protocol.Protostar.Oracle       (RandomOracle (..))

-- | Accumulator scheme for V_NARK as described in Chapter 3.4 of the Protostar paper
--
-- TODO: define the initial accumulator
--
class AccumulatorScheme f i m c d k a where
  prover   :: a
           -> Accumulator f i m c k                      -- accumulator
           -> InstanceProofPair f i m c k                -- instance-proof pair (pi, π)
           -> (Accumulator f i m c k, Vector (d - 1) c)  -- updated accumulator and accumulation proof

  verifier :: i f                                        -- Public input
           -> Vector k c                                 -- NARK proof π.x
           -> AccumulatorInstance f i c k                -- accumulator instance acc.x
           -> AccumulatorInstance f i c k                -- updated accumulator instance acc'.x
           -> Vector (d - 1) c                           -- accumulation proof E_j
           -> (f, i f, Vector (k-1) f, Vector k c, c)    -- returns zeros if the accumulation proof is correct

  decider  :: a
           -> Accumulator f i m c k                      -- final accumulator
           -> (Vector k c, c)                            -- returns zeros if the final accumulator is valid

instance
    ( AlgebraicMap f i d a
    , AlgebraicMap (PU.PolyVec f (d + 1)) i d a
    , Ring f
    , Zip i
    , KnownNat (d - 1)
    , KnownNat (d + 1)
    , Scale f c
    , HomomorphicCommit [f] c
    , RandomOracle (i f) f    -- Random oracle for compressing public input
    , RandomOracle c f        -- Random oracle ρ_NARK
    , KnownNat k
    ) => AccumulatorScheme f i [f] c d k (FiatShamir (CommitOpen a)) where
  prover (FiatShamir (CommitOpen sps)) acc (InstanceProofPair pubi (NARKProof pi_x pi_w)) =
        (Accumulator (AccumulatorInstance pi'' ci'' ri'' eCapital' mu') m_i'', pf)
      where
          r_0 :: f
          r_0 = oracle pubi

          -- Fig. 3, step 1
          r_i :: Vector (k-1) f
          r_i = transcriptFiatShamir r_0 pi_x

          -- Fig. 3, step 2

          -- X + mu as a univariate polynomial
          polyMu :: PU.PolyVec f (d + 1)
          polyMu = PU.polyVecLinear one (acc^.x^.mu)

          -- X * pi + pi' as a list of univariate polynomials
          polyPi :: i (PU.PolyVec f (d + 1))
          polyPi = zipWith (PU.polyVecLinear @f) pubi (acc^.x^.pi)

          -- X * mi + mi'
          polyW :: Vector k [PU.PolyVec f (d + 1)]
          polyW = zipWith (zipWith (PU.polyVecLinear @f)) pi_w (acc^.w)

          -- X * ri + ri'
          polyR :: Vector (k-1) (PU.PolyVec f (d + 1))
          polyR = zipWith (P.flip PU.polyVecLinear) (acc^.x^.r) r_i

          -- The @l x d+1@ matrix of coefficients as a vector of @l@ univariate degree-@d@ polynomials
          --
          e_uni :: [PU.PolyVec f (d + 1)]
          e_uni = algebraicMap @_ @_ @d sps polyPi polyW polyR polyMu

          -- e_all are coefficients of degree-j homogenous polynomials where j is from the range [0, d]
          e_all = transpose $ DV.toList . PU.fromPolyVec <$> e_uni

          -- e_j are coefficients of degree-j homogenous polynomials where j is from the range [1, d - 1]
          e_j :: Vector (d-1) [f]
          e_j = unsafeToVector $ P.tail . P.init $ e_all

          -- Fig. 3, step 3
          pf = hcommit <$> e_j

          -- Fig. 3, step 4
          alpha :: f
          alpha = oracle (acc^.x, pubi, pi_x, pf)

          -- Fig. 3, steps 5, 6
          mu'   = alpha + acc^.x^.mu
          pi''  = zipWith (+) (fmap (* alpha) pubi) (acc^.x^.pi)
          ri''  = scale alpha r_i  + acc^.x^.r
          ci''  = scale alpha pi_x + acc^.x^.c
          m_i'' = zipWith (+) (scale alpha pi_w) (acc^.w)

          -- Fig. 3, step 7
          eCapital' = acc^.x^.e + sum (mapWithIx (\i a -> scale (alpha ^ (i+1)) a) pf)


  verifier pubi c_i acc acc' pf = (muDiff, piDiff, riDiff, ciDiff, eDiff)
      where
          -- Fig. 4, step 1
          r_i :: Vector (k-1) f
          r_i = unsafeToVector $ P.tail $ P.tail $ P.scanl (P.curry oracle) (oracle pubi) $ toList c_i

          -- Fig. 4, step 2
          alpha :: f
          alpha = oracle (acc, pubi, c_i, pf)

          -- Fig. 4, step 3
          mu'  = alpha + acc^.mu
          pi'' = zipWith (+) (fmap (* alpha) pubi) (acc^.pi)
          ri'' = zipWith (+) (scale alpha r_i)  (acc^.r)
          ci'' = zipWith (+) (scale alpha c_i)  (acc^.c)

          -- Fig 4, step 4
          muDiff = acc'^.mu - mu'
          piDiff = zipWith (-) (acc'^.pi) pi''
          riDiff = zipWith (-) (acc'^.r)  ri''
          ciDiff = acc'^.c  - ci''

          -- Fig 4, step 5
          eDiff = acc'^.e - (acc^.e + sum (mapWithIx (\i a -> scale (alpha ^ (i+1)) a) pf))

  decider (FiatShamir (CommitOpen sps)) acc = (commitsDiff, eDiff)
      where
          -- Fig. 5, step 1
          commitsDiff = zipWith (\cm m_acc -> cm - hcommit m_acc) (acc^.x^.c) (acc^.w)

          -- Fig. 5, step 2
          err :: [f]
          err = algebraicMap @_ @_ @d sps (acc^.x^.pi) (acc^.w) (acc^.x^.r) (acc^.x^.mu)


          -- Fig. 5, step 3
          eDiff = (acc^.x^.e) - hcommit err
