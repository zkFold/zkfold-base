{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.AccumulatorScheme where

import           Control.DeepSeq                             (NFData)
import           Control.Lens                                ((^.))
import           Data.List                                   (transpose)
import qualified Data.Vector                                 as DV
import           GHC.Generics                                (Generic)
import           Prelude                                     (type (~), ($), (.), (<$>))
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
           -> (f, KeyScale f)             -- Commitment key ck and scaling factor
           -> Accumulator pi f c m        -- final accumulator
           -> ([c], c)                    -- returns zeros if the final accumulator is valid

data KeyScale f = KeyScale f f
    deriving (P.Show, Generic, NFData)

-- | Class describing types which can form a polynomial linear combination:
-- linearCombination a1 a2 -> a1 * X + a2
--
class LinearCombination a b where
    linearCombination :: a -> a -> b

-- | Same as above, but with a coefficient known at runtime
-- linearCombination coeff b1 b2 -> b1 * coeff + b2
--
class LinearCombinationWith a b where
    linearCombinationWith :: a -> b -> b -> b

instance (Scale f a, AdditiveSemigroup a) => LinearCombinationWith f [a] where
    linearCombinationWith f = P.zipWith (\a b -> scale f a + b)

instance
    ( AdditiveGroup i
    , AdditiveGroup c
    , AdditiveSemigroup m
    , Ring f
    , Scale f c
    , Scale f m
    , MapInput f a ~ i
    , deg ~ Degree (CommitOpen m c a) + 1
    , KnownNat deg
    , LinearCombination (MapMessage f a) (MapMessage (PU.PolyVec f deg) a)
    , LinearCombination (MapInput f a) (MapInput (PU.PolyVec f deg) a)
    , LinearCombinationWith f (MapInput f a)
    , MapMessage f a ~ m
    , AlgebraicMap f (CommitOpen m c a)
    , AlgebraicMap (PU.PolyVec f deg) a
    , RandomOracle c f                                    -- Random oracle ρ_NARK
    , RandomOracle i f                                    -- Random oracle for compressing public input
    , HomomorphicCommit f [m] c
    , HomomorphicCommit f [f] c
    ) => AccumulatorScheme i f c m (FiatShamir f (CommitOpen m c a)) where
  prover (FiatShamir (CommitOpen _ sps)) ck acc (InstanceProofPair pubi (NARKProof pi_x pi_w)) =
        (Accumulator (AccumulatorInstance pi'' ci'' ri'' eCapital' mu') mi'', eCapital_j)
      where
          -- Fig. 3, step 1
          r_i :: [f]
          r_i = P.tail $ P.scanl (P.curry oracle) (oracle pubi) (zero : pi_x)

          -- Fig. 3, step 2

          -- X + mu as a univariate polynomial
          polyMu :: PU.PolyVec f deg
          polyMu = PU.polyVecLinear (acc^.x^.mu) one

          -- X * pi + pi' as a list of univariate polynomials
          polyPi = linearCombination pubi (acc^.x^.pi)

          -- X * mi + mi'
          polyW = P.zipWith linearCombination pi_w (acc^.w)

          -- X * ri + ri'
          polyR :: [PU.PolyVec f deg]
          polyR = P.zipWith (P.flip PU.polyVecLinear) (acc^.x^.r) r_i

          -- The @l x d+1@ matrix of coefficients as a vector of @l@ univariate degree-@d@ polynomials
          --
          e_uni :: [PU.PolyVec f deg]
          e_uni = algebraicMap @(PU.PolyVec f deg) sps polyPi polyW polyR polyMu

          -- e_all are coefficients of degree-j homogenous polynomials where j is from the range [0, d]
          e_all = transpose $ (DV.toList . PU.fromPolyVec) <$> e_uni

          -- e_j are coefficients of degree-j homogenous polynomials where j is from the range [1, d - 1]
          e_j :: [[f]]
          e_j = P.tail $ P.init $ e_all

          -- Fig. 3, step 3
          eCapital_j = hcommit ck <$> e_j

          -- Fig. 3, step 4
          alpha :: f
          alpha = oracle (acc^.x, pubi, pi_x, eCapital_j)

          -- Fig. 3, steps 5, 6
          mu'  = alpha + acc^.x^.mu
          pi'' = linearCombinationWith alpha pubi $ acc^.x^.pi
          ri'' = linearCombinationWith alpha r_i  $ acc^.x^.r
          ci'' = linearCombinationWith alpha pi_x $ acc^.x^.c
          mi'' = linearCombinationWith alpha pi_w $ acc^.w

          -- Fig. 3, step 7
          eCapital' = acc^.x^.e + sum (P.zipWith (\e' p -> scale (alpha ^ p) e') eCapital_j [1::Natural ..])


  verifier pubi c_i acc acc' pf = (muDiff, piDiff, riDiff, ciDiff, eDiff)
      where
          -- Fig. 4, step 1
          r_i :: [f]
          r_i = P.tail $ P.scanl (P.curry oracle) (oracle pubi) (zero : c_i)

          -- Fig. 4, step 2
          alpha :: f
          alpha = oracle (acc, pubi, c_i, pf)

          -- Fig. 4, step 3
          mu'  = alpha + acc^.mu
          pi'' = linearCombinationWith alpha pubi $ acc^.pi
          ri'' = linearCombinationWith alpha r_i  $ acc^.r
          ci'' = linearCombinationWith alpha c_i  $ acc^.c

          -- Fig 4, step 4
          muDiff = acc'^.mu - mu'
          piDiff = acc'^.pi - pi''
          riDiff = acc'^.r  - ri''
          ciDiff = acc'^.c  - ci''

          -- Fig 4, step 5
          eDiff = acc'^.e - (acc^.e + sum (P.zipWith scale ((\p -> alpha^p) <$> [1 :: Natural ..]) pf))

  decider (FiatShamir sps) (ck, KeyScale ef _) acc = (commitsDiff, eDiff)
      where
          -- Fig. 5, step 1
          commitsDiff = P.zipWith (\cm m_acc -> cm - hcommit (scale (acc^.x^.mu) ck) [m_acc]) (acc^.x^.c) (acc^.w)

          -- Fig. 5, step 2
          err :: [f]
          err = algebraicMap @f sps (acc^.x^.pi) [Open $ acc^.w] (acc^.x^.r) (acc^.x^.mu)


          -- Fig. 5, step 3
          eDiff = (acc^.x^.e) - hcommit (scale ef ck) err
