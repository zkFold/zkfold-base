{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.AccumulatorScheme where

import           Control.Lens                                    ((^.))
import qualified Data.Vector                                     as DV
import           Debug.Trace
import           GHC.IsList                                      (IsList (..))
import           Prelude                                         (fmap, otherwise, type (~), ($), (&&), (.), (<$>), (<),
                                                                  (<=), (==))
import qualified Prelude                                         as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Algebra.Polynomials.Multivariate    as PM
import qualified ZkFold.Base.Algebra.Polynomials.Univariate      as PU
import qualified ZkFold.Base.Data.Vector                         as V
import           ZkFold.Base.Protocol.Protostar.Accumulator
import           ZkFold.Base.Protocol.Protostar.Commit       (Commit (..))
import           ZkFold.Base.Protocol.Protostar.CommitOpen   (CommitOpen (..), CommitOpenProverMessage (..))
import           ZkFold.Base.Protocol.Protostar.FiatShamir   (FiatShamir (..))
import           ZkFold.Base.Protocol.Protostar.Oracle       (RandomOracle (..))
import           ZkFold.Base.Protocol.Protostar.SpecialSound (Input, LMap, SpecialSoundProtocol (..))
import           ZkFold.Prelude                                  (length, (!!))

traceP :: P.Show a => P.String -> a -> a
traceP s a = trace (s P.<> P.show a) a

-- | Accumulator scheme for V_NARK as described in Chapter 3.4 of the Protostar paper
--
class AccumulatorScheme i f c m a where
  prover   :: a
           -> f                          -- Commitment key ck
           -> Accumulator i f c m        -- accumulator
           -> InstanceProofPair i c m    -- instance-proof pair (pi, π)
           -> (Accumulator i f c m, [c]) -- updated accumulator and accumulation proof

  verifier :: i                          -- Public input
           -> [c]                        -- NARK proof π.x
           -> AccumulatorInstance i f c  -- accumulator instance acc.x
           -> AccumulatorInstance i f c  -- updated accumulator instance acc'.x
           -> [c]                        -- accumulation proof E_j
           -> P.Bool

  decider  :: a
           -> f                     -- Commitment key ck
           -> Accumulator i f c m   -- accumulator
           -> P.Bool

instance
    ( P.Eq c
    , P.Eq i
    , P.Show f
    , P.Show c 
    , P.Show i
    , f ~ m   -- If they are actually not the same, replace m with hashes.
    , AdditiveGroup c
    , Ring f
    , Scale f c
    , IsList (Input f (CommitOpen f c a))
    , Input f a ~ i
    , Item i ~ f
    , ProverMessage Natural a ~ m
    , KnownNat (Degree (CommitOpen f c a))
    , SpecialSoundProtocol f (CommitOpen f c a)
    , RandomOracle c f                                    -- Random oracle ρ_NARK
    , RandomOracle i f                                    -- Random oracle for compressing public input
    , HomomorphicCommit f [m] c
    ) => AccumulatorScheme i f c m (FiatShamir f (CommitOpen f c a)) where
  prover fs@(FiatShamir sps i) ck acc ip@(InstanceProofPair pubi (NARKProof pi_x pi_w)) = -- trace traceStr $ -- P.undefined
        (Accumulator (AccumulatorInstance (fromList pi'') ci'' ri'' eCapital' mu') mi'', eCapital_j)
      where
          traceStr :: P.String
          traceStr = P.unlines
            [ "Acc " P.<> P.show acc
            , "Instance proof " P.<> P.show ip
            , "r_i " P.<> P.show r_i
            , "k " P.<> P.show k
       --     , P.show $ PU.toPoly $ DV.fromList [(acc^.w) !! (2 -! l_in), pi_w !! (2 -! l_in)]
       --     , P.show (ixToPoly 2)
       --     , P.show (ixToPoly 2 * ixToPoly 2)
       --     , "mappedVars " P.<> P.show mappedVars
       --     , "e_uni " P.<> P.show e_uni
       --     , "e_j " P.<> P.show e_j
            ]

          -- Fig. 3, step 1
          r_i :: [f]
          r_i = P.tail $ P.scanl (P.curry oracle) (oracle pubi) (zero : pi_x)

          -- Fig. 3, step 2
          
          f_sps = degreeDecomposition @(Degree (CommitOpen f c a)) $ algebraicMap @f sps pubi [Open pi_w] r_i 

          -- X + mu as a univariate polynomial
          xMu :: PU.Poly f
          xMu = PU.toPoly $ DV.fromList [acc^.x^.mu, one]

          d :: Natural
          d = outputLength @f sps

          k :: Natural
          k = rounds @f sps

          l_in :: Natural
          l_in = length $ toList $ (acc^.x^.pi)

          ixToPoly :: Natural -> PU.Poly f
          ixToPoly n
            | n < l_in      = PU.toPoly $ DV.fromList [(toList $ acc^.x^.pi) !! n, toList pubi !! n]        -- X * pi + pi'
            | n <= k + l_in = PU.toPoly $ DV.fromList [(acc^.w) !! (n -! l_in), pi_w !! (n -! l_in)]        -- X * mi + mi'
            | otherwise     = PU.toPoly $ DV.fromList [(acc^.x^.r) !! (n -! k -! l_in -! 1), r_i !! (n -! k -! l_in -! 1)]  -- X * ri + ri'

          -- The @lxd@ matrix of coefficients as a vector of @l@ univariate degree-@d@ polynomials
          --
          mappedVars = fmap (PM.evalPolynomial PM.evalMonomial ixToPoly) <$> f_sps

          e_uni :: [PU.Poly f]
          e_uni = P.foldl (P.zipWith (+)) (P.repeat zero) $ V.mapWithIx (\j p -> ((xMu ^ (d -! j)) *) <$> p) $ mappedVars

          e_all = (DV.toList . PU.fromPoly) <$> e_uni

          e_j :: [[f]]
          e_j = P.tail e_all

          -- Fig. 3, step 3
          eCapital_j = hcommit ck <$> e_j

          -- Fig. 3, step 4
          alpha :: f
          alpha = oracle (acc^.x, pubi, pi_x, eCapital_j)

          -- Fig. 3, steps 5, 6
          mu'  = alpha            + acc^.x^.mu
          pi'' = P.zipWith (\i_pi i_acc -> scale alpha i_pi + i_acc) (toList pubi) $ toList (acc^.x^.pi)
          ri'' = P.zipWith (\r_pi r_acc -> scale alpha r_pi + r_acc) r_i  $ acc^.x^.r
          ci'' = P.zipWith (\c_pi c_acc -> scale alpha c_pi + c_acc) pi_x $ acc^.x^.c
          mi'' = P.zipWith (\m_pi m_acc -> scale alpha m_pi + m_acc) pi_w $ acc^.w

          -- Fig. 3, step 7
          eCapital' = acc^.x^.e + sum (P.zipWith (\e' p -> scale (alpha ^ p) e') eCapital_j [1::Natural ..])


  verifier pubi c_i acc acc' pf = P.and [muEq, piEq, riEq, ciEq, eEq]
      where
          -- Fig. 4, step 1
          r_i :: [f]
          r_i = P.tail $ P.scanl (P.curry oracle) (oracle pubi) (zero : c_i)

          -- Fig. 4, step 2
          alpha :: f
          alpha = oracle (acc, pubi, c_i, pf)

          -- Fig. 4, step 3
          mu'  = alpha + acc^.mu
          pi'' = P.zipWith (\i_pi pi_acc -> scale alpha i_pi + pi_acc) (toList pubi) $ (toList $ acc^.pi)
          ri'' = P.zipWith (\r_pi r_acc  -> scale alpha r_pi + r_acc)  r_i  $ acc^.r
          ci'' = P.zipWith (\c_pi c_acc  -> scale alpha c_pi + c_acc)  c_i  $ acc^.c

          -- Fig 4, step 4
          muEq = acc'^.mu == mu'
          piEq = acc'^.pi == fromList pi''
          riEq = acc'^.r  == ri''
          ciEq = acc'^.c  == ci''

          -- Fig 4, step 5
          eEq = acc'^.e == acc^.e + sum (P.zipWith scale ((\p -> alpha^p) <$> [1 :: Natural ..]) pf)

  --decider (FiatShamir sps i) ck acc = traceShow (commitsEq) $ commitsEq && eEq
  decider (FiatShamir sps i) ck acc = commitsEq && eEq
      where
          d :: Natural
          d = outputLength @f sps

          k :: Natural
          k = rounds @f sps

          -- Fig. 5, step 1
          commitsEq = P.and $ P.zipWith (\cm m_acc -> cm == hcommit (scale (acc^.x^.mu) ck) [m_acc]) (acc^.x^.c) (acc^.w)

          -- Fig. 5, step 2
          f_sps = mulDeg (acc^.x^.mu) d <$> algebraicMap @f sps (acc^.x^.pi) [Open $ acc^.w] (acc^.x^.r)

          l_in :: Natural
          l_in = length $ toList (acc^.x^.pi)

          ixToVal :: Natural -> f
          ixToVal n
            | n < l_in      = toList (acc^.x^.pi) !! n               -- pi
            | n <= k + l_in = (acc^.w) !! (n -! l_in)                -- mi
            | otherwise     = (acc^.x^.r) !! (n -! k  -! l_in -! 1)  -- ri

          err = PM.evalPolynomial PM.evalMonomial ixToVal <$> f_sps

          -- Fig. 5, step 3
          eEq = acc^.x^.e == hcommit ck err

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
degreeDecomposition lmap = V.generate degree_j
    where
        degree_j :: Natural -> LMap f
        degree_j j = P.fmap (leaveDeg j) lmap

        leaveDeg :: Natural -> PM.Poly f Natural Natural -> PM.Poly f Natural Natural
        leaveDeg j (PM.P monomials) = PM.P $ P.filter (\(_, m) -> deg m == j) monomials

deg :: PM.Mono Natural Natural -> Natural
deg (PM.M m) = sum m
