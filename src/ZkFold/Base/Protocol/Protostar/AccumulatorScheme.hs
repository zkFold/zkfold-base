{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.AccumulatorScheme where

import           Control.Lens                                 ((^.))
import           Data.Functor.Rep                             (Representable (tabulate))
import qualified Data.Vector                                  as DV
import           Prelude                                      (fmap, otherwise, type (~), ($), (&&), (.), (<$>), (<=),
                                                               (==))
import qualified Prelude                                      as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Algebra.Polynomials.Multivariate as PM
import qualified ZkFold.Base.Algebra.Polynomials.Univariate   as PU
import qualified ZkFold.Base.Data.Vector                      as V
import           ZkFold.Base.Protocol.Protostar.Accumulator
import           ZkFold.Base.Protocol.Protostar.CommitOpen    (CommitOpen (..))
import           ZkFold.Base.Protocol.Protostar.FiatShamir    (FiatShamir (..))
import           ZkFold.Base.Protocol.Protostar.Oracle        (RandomOracle (..))
import           ZkFold.Base.Protocol.Protostar.SpecialSound  (Input, LMap, ProverMessage, SpecialSoundProtocol (..))
import           ZkFold.Prelude                               ((!!))


-- | Accumulator scheme for V_NARK as described in Chapter 3.4 of the Protostar paper
--
class AccumulatorScheme f c m a where
  commit   :: a -> [m] -> c

  prover   :: a                        -- input commitment key
           -> Accumulator f c m        -- accumulator
           -> InstanceProofPair f c m  -- instance-proof pair (pi, π)
           -> (Accumulator f c m, [c]) -- updated accumulator and accumulation proof

  verifier :: f                        -- Public input
           -> [c]                      -- NARK proof π.x
           -> AccumulatorInstance f c  -- accumulator instance acc.x
           -> AccumulatorInstance f c  -- updated accumulator instance acc'.x
           -> [c]                      -- accumulation proof E_j
           -> P.Bool

  decider  :: a                   -- Commitment key ck
           -> Accumulator f c m   -- accumulator
           -> P.Bool

instance
    ( Input f a ~ f
    , ProverMessage f a ~ m
    , f ~ m -- TODO: Seems off but I really have no idea how to compile the code without it
    , P.Eq c
    , AdditiveGroup c
    , Ring m
    , Scale m c
    , Input m (FiatShamir m (CommitOpen m c a)) ~ m
    , ProverMessage Natural (FiatShamir m (CommitOpen m c a)) ~ m
    , VerifierMessage Natural (FiatShamir m (CommitOpen m c a)) ~ m
    , KnownNat (Degree (FiatShamir f (CommitOpen f c a)))
    , SpecialSoundProtocol f (FiatShamir f (CommitOpen f c a))
    , RandomOracle (f, c) f                                  -- Random oracle ρ_NARK
    , RandomOracle (AccumulatorInstance f c, f, [c], [c]) f  -- Random oracle ρ_acc
    ) => AccumulatorScheme f c m (FiatShamir f (CommitOpen f c a)) where
  commit (FiatShamir (CommitOpen cm _) _) = cm

  prover sps@(FiatShamir (CommitOpen cm _) _) acc (InstanceProofPair pubi (NARKProof pi_x pi_w)) =
      (Accumulator (AccumulatorInstance pi'' ci'' ri'' eCapital' mu') mi'', eCapital_j)
      where
          -- Fig. 3, step 1
          r_i :: [f]
          r_i = P.tail $ P.scanl (P.curry oracle) pubi (zero : pi_x)

          -- Fig. 3, step 2
          f_sps = degreeDecomposition @(Degree (FiatShamir f (CommitOpen f c a))) $ algebraicMap @f sps pubi (acc^.x^.r) (acc^.w)

          -- X + mu as a univariate polynomial
          xMu :: PU.Poly f
          xMu = PU.toPoly $ DV.fromList [acc^.x^.mu, one]

          d :: Natural
          d = outputLength @f sps

          k :: Natural
          k = rounds @f sps

          ixToPoly :: Natural -> PU.Poly f
          ixToPoly n
            | n == 0    = PU.toPoly $ DV.fromList [acc^.x^.pi, pubi]                                   -- X * pi + pi'
            | n <= k    = PU.toPoly $ DV.fromList [(acc^.w) !! (n -! 1), pi_w !! (n -! 1)]             -- X * mi + mi'
            | otherwise = PU.toPoly $ DV.fromList [(acc^.x^.r) !! (n -! k -! 1), r_i !! (n -! k -! 1)] -- X * ri + ri'

          -- The @lxd@ matrix of coefficients as a vector of @l@ univariate degree-@d@ polynomials
          --
          e_uni :: [PU.Poly f]
          e_uni = P.foldl (P.liftA2 (+)) (P.pure zero) $ V.mapWithIx (\j p -> ((xMu ^ (d -! j)) *) <$> p) $ fmap (PM.evalPolynomial PM.evalMonomial ixToPoly) <$> f_sps

          e_all = (DV.toList . PU.fromPoly) <$> e_uni

          e_j :: [[f]]
          e_j = P.tail e_all

          -- Fig. 3, step 3
          eCapital_j = cm <$> e_j

          -- Fig. 3, step 4
          alpha :: f
          alpha = oracle (acc^.x, pubi, pi_x, eCapital_j)

          -- Fig. 3, steps 5, 6
          mu'  = alpha            + acc^.x^.mu
          pi'' = scale alpha pubi + acc^.x^.pi
          ri'' = P.zipWith (\rl r' -> scale alpha rl + r') r_i  $ acc^.x^.r
          ci'' = P.zipWith (\cl c' -> scale alpha cl + c') pi_x $ acc^.x^.c
          mi'' = P.zipWith (\ml m' -> scale alpha ml + m') pi_w $ acc^.w

          -- Fig. 3, step 7
          eCapital' = acc^.x^.e + sum (P.zipWith (\e' p -> scale (alpha ^ p) e') eCapital_j [1::Natural ..])


  verifier pubi c_i acc acc' pf = P.and [muEq, piEq, riEq, ciEq, eEq]
      where
          -- Fig. 4, step 1
          r_i :: [f]
          r_i = P.tail $ P.scanl (P.curry oracle) pubi (zero : c_i)

          -- Fig. 4, step 2
          alpha :: f
          alpha = oracle (acc, pubi, c_i, pf)

          -- Fig. 4, step 3
          mu'  = alpha            + acc^.mu
          pi'' = scale alpha pubi + acc^.pi
          ri'' = P.zipWith (\rl r' -> scale alpha rl + r') r_i $ acc^.r
          ci'' = P.zipWith (\cl c' -> scale alpha cl + c') c_i $ acc^.c

          -- Fig 4, step 4
          muEq = acc'^.mu == mu'
          piEq = acc'^.pi == pi''
          riEq = acc'^.r  == ri''
          ciEq = acc'^.c  == ci''

          -- Fig 4, step 5
          eEq = acc'^.e == acc^.e + sum (P.zipWith scale ((\p -> alpha^p) <$> [1 :: Natural ..]) pf)

  decider sps@(FiatShamir (CommitOpen cm _) _) acc = commitsEq && eEq
      where
          d :: Natural
          d = outputLength @f sps

          k :: Natural
          k = rounds @f sps


          -- Fig. 5, step 1
          commitsEq = P.and $ P.zipWith (\cl m -> cm [m] == cl) (acc^.x^.c) (acc^.w)

          -- Fig. 5, step 2
          f_sps = mulDeg (acc^.x^.mu) d <$> algebraicMap @f sps (acc^.x^.pi) (acc^.x^.r) (acc^.w)

          ixToVal :: Natural -> f
          ixToVal n
            | n == 0    = acc^.x^.pi                   -- pi
            | n <= k    = (acc^.w) !! (n -! 1)         -- mi
            | otherwise = (acc^.x^.r) !! (n -! k -! 1) -- ri

          err = PM.evalPolynomial PM.evalMonomial ixToVal <$> f_sps

          -- Fig. 5, step 3
          eEq = acc^.x^.e == cm err

mulDeg
    :: MultiplicativeSemigroup f
    => Exponent f Natural
    => f
    -> Natural
    -> PM.Poly f Natural Natural
    -> PM.Poly f Natural Natural
mulDeg f d (PM.P monomials) = PM.P $ (\(coeff, m) -> (f ^ (d -! deg m) * coeff, m)) <$> monomials

-- | Decomposes an algebraic map into homogenous degree-j maps for j from 0 to @n@
--
degreeDecomposition :: forall n f . KnownNat n => LMap f -> V.Vector n (LMap f)
degreeDecomposition lmap = tabulate (degree_j . toConstant)
    where
        degree_j :: Natural -> LMap f
        degree_j j = P.fmap (leaveDeg j) lmap

        leaveDeg :: Natural -> PM.Poly f Natural Natural -> PM.Poly f Natural Natural
        leaveDeg j (PM.P monomials) = PM.P $ P.filter (\(_, m) -> deg m == j) monomials

deg :: PM.Mono Natural Natural -> Natural
deg (PM.M m) = sum m
