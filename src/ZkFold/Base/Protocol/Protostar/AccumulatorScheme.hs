{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.AccumulatorScheme where

import           Control.Lens                                 ((^.))
import           Data.List                                    (foldl', transpose)
import qualified Data.Vector                                  as DV
import           Debug.Trace
import           GHC.IsList                                   (IsList (..))
import           Prelude                                      (fmap, otherwise, type (~), ($), (&&), (.), (<$>), (<),
                                                               (<=), (==))
import qualified Prelude                                      as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Algebra.Polynomials.Multivariate as PM
import qualified ZkFold.Base.Algebra.Polynomials.Univariate   as PU
import qualified ZkFold.Base.Data.Vector                      as V
import           ZkFold.Base.Protocol.Protostar.Accumulator
import           ZkFold.Base.Protocol.Protostar.Commit        (Commit (..), HomomorphicCommit (..))
import           ZkFold.Base.Protocol.Protostar.CommitOpen    (CommitOpen (..), CommitOpenProverMessage (..))
import           ZkFold.Base.Protocol.Protostar.FiatShamir    (FiatShamir (..))
import           ZkFold.Base.Protocol.Protostar.Oracle        (RandomOracle (..))
import           ZkFold.Base.Protocol.Protostar.SpecialSound  (Input, SpecialSoundProtocol (..))
import           ZkFold.Prelude                               (length, take, (!!))

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
    , P.Eq f
    , P.Show i
    , P.Show f
    , P.Show c
    , P.Show m
    , AdditiveGroup c
    , AdditiveSemigroup m
    , Ring f
    , Scale f c
    , Scale f m
    , IsList (Input (PU.Poly f) (CommitOpen f c a))
    , IsList (Input f (CommitOpen f c a))
    , Item (Input (PU.Poly f) (CommitOpen f c a)) ~ PU.Poly f
    , IsList (Input (PU.Poly f) a)
    , Input f a ~ i
    , Item i ~ f
    , Item (Input (PU.Poly f) a) ~ PU.Poly f
    , ProverMessage f a ~ m
    , KnownNat (Degree (CommitOpen f c a))
    , KnownNat (Degree (CommitOpen f c a) + 1)
    , SpecialSoundProtocol f (CommitOpen f c a)
    , RandomOracle c f                                    -- Random oracle ρ_NARK
    , RandomOracle i f                                    -- Random oracle for compressing public input
    , HomomorphicCommit f [m] c
    , HomomorphicCommit f [f] c
    ) => AccumulatorScheme i f c m (FiatShamir f (CommitOpen f c a)) where
  prover fs@(FiatShamir sps i) ck acc ip@(InstanceProofPair pubi (NARKProof pi_x pi_w)) =  trace traceStr $ -- P.undefined
        (Accumulator (AccumulatorInstance (fromList pi'') ci'' ri'' eCapital' mu') mi'', eCapital_j)
      where
          traceStr :: P.String
          traceStr = P.unlines
            [ "Acc " P.<> P.show acc
            , "Instance proof " P.<> P.show ip
            , "r_i " P.<> P.show r_i
            , "e_uni " P.<> P.show e_uni
            , "e_all " P.<> P.show e_all
            , "e_j " P.<> P.show e_j
            , "e_prev " P.<> P.show e_prev
            , "commit " P.<> P.show (hcommit @_ @_ @c ck e_prev)
            , "e_capital " P.<> P.show eCapital'
            , "evaluated " P.<> P.show (P.flip PU.evalPoly alpha <$> e_uni)
            , "commit evaluated " P.<> P.show (hcommit @_ @_ @c ck $ P.flip PU.evalPoly alpha <$> e_uni)
            ]

          d = value @(Degree (CommitOpen f c a))

          -- Fig. 3, step 1
          r_i :: [f]
          r_i = P.tail $ P.scanl (P.curry oracle) (oracle pubi) (zero : pi_x)

          -- Fig. 3, step 2

          -- X + mu as a univariate polynomial
          polyMu :: PU.Poly f
          polyMu = PU.toPoly $ DV.fromList [acc^.x^.mu, one]
    
          -- X * pi + pi' as a list of univariate polynomials
          polyPi = fromList $ P.zipWith (\accPi proofPi -> PU.toPoly $ DV.fromList [accPi, proofPi]) (toList $ acc^.x^.pi) (toList pubi) 

          -- X * mi + mi'
          polyW = P.undefined
          -- PU.toPoly $ DV.fromList [(acc^.w) !! (n -! l_in), pi_w !! (n -! l_in)]

          -- X * ri + ri'
          polyR = P.undefined
          -- PU.toPoly $ DV.fromList [(acc^.x^.r) !! (n -! k -! l_in), r_i !! (n -! k -! l_in)]  

          -- The @l x d+1@ matrix of coefficients as a vector of @l@ univariate degree-@d@ polynomials
          --
          e_uni :: [PU.Poly f]
          e_uni = algebraicMap @(PU.Poly f) sps polyPi polyW polyR polyMu 

          -- e_all are coefficients of degree-j homogenous polynomials where j is from the range [0, d]
          e_all = transpose $ (take (d + 1) . (P.<> (P.repeat zero)) . DV.toList . PU.fromPoly) <$> e_uni

          -- e_j are coefficients of degree-j homogenous polynomials where j is from the range [1, d - 1]
          e_j :: [[f]]
          e_j = P.tail $ P.init $ e_all

          e_prev = P.head e_all

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

  decider (FiatShamir sps i) ck acc = traceShow (commitsEq, eEq) $ commitsEq && eEq
  --decider (FiatShamir sps i) ck acc = commitsEq && eEq
      where
          d :: Natural
          d = value @(Degree (CommitOpen f c a))

          k :: Natural
          k = rounds @f sps

          -- Fig. 5, step 1
          commitsEq = P.and $ P.zipWith (\cm m_acc -> cm == hcommit (scale (acc^.x^.mu) ck) [m_acc]) (acc^.x^.c) (acc^.w)

          -- Fig. 5, step 2
          err :: [f]
          err = algebraicMap @f sps (acc^.x^.pi) [Open $ acc^.w] (acc^.x^.r) (acc^.x^.mu)


          -- Fig. 5, step 3
          --eEq = (acc^.x^.e) == hcommit (scale (acc^.x^.mu) ck) err
          eEq = (acc^.x^.e) == hcommit ck err
