{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module ZkFold.Base.Protocol.Protostar.Fold where


import           Control.DeepSeq                                     (NFData)
import           Control.Lens                                        ((^.))
import           Data.Map.Strict                                     (Map)
import qualified Data.Map.Strict                                     as M
import           GHC.Generics                                        (Generic)
import           Prelude                                             (and, otherwise, type (~), ($), (<$>), (<*>), (==))
import qualified Prelude                                             as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Algebra.Polynomials.Univariate          as PU
import           ZkFold.Base.Data.Vector                             (Vector)
import           ZkFold.Base.Protocol.Protostar.Accumulator
import qualified ZkFold.Base.Protocol.Protostar.AccumulatorScheme    as Acc
import           ZkFold.Base.Protocol.Protostar.ArithmeticCircuit
import           ZkFold.Base.Protocol.Protostar.Commit
import           ZkFold.Base.Protocol.Protostar.CommitOpen
import           ZkFold.Base.Protocol.Protostar.FiatShamir
import           ZkFold.Base.Protocol.Protostar.Oracle
import qualified ZkFold.Base.Protocol.Protostar.SpecialSound         as SPS
import           ZkFold.Prelude                                      (replicate)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Data.FieldElement                   (FieldElement)

data FoldResult n c a
    = FoldResult
    { output          :: Vector n a
    , lastAccumulator :: Accumulator (Vector n a) a c (Map Natural a)
    , verifierOutput  :: P.Bool
    , deciderOutput   :: P.Bool
    } deriving (P.Show, Generic, NFData)

type FS_CM n c a = FiatShamir a (CommitOpen a c (RecursiveCircuit n a))

transform
    :: forall n c a
    .  HomomorphicCommit a [Map Natural a] c
    => a
    -> RecursiveCircuit n a
    -> Vector n a
    -> FS_CM n c a
transform ck rc v = FiatShamir (CommitOpen (hcommit ck) rc) v

-- | These instances might seem off, but accumulator scheme requires this exact behaviour
--
instance AdditiveSemigroup a => AdditiveSemigroup (Map Natural a) where
    (+) = M.unionWith (+)

instance AdditiveMonoid a => AdditiveMonoid (Map Natural a) where
    zero = M.empty

instance (Ring a, P.Eq a) => Acc.LinearCombination (Map Natural a) (Map Natural (PU.Poly a)) where
    linearCombination mx ma = M.unionWith (+) (PU.monomial 1 <$> mx) (PU.constant <$> ma)

instance (Ring a, P.Eq a, KnownNat n) => Acc.LinearCombination (Vector n a) (Vector n (PU.Poly a)) where
    linearCombination mx ma = (+) <$> (PU.monomial 1 <$> mx) <*> (PU.constant <$> ma)

instance (Ring a, KnownNat n) => Acc.LinearCombinationWith a (Vector n a) where
    linearCombinationWith coeff a b = (+) <$> (P.fmap (coeff *) a) <*> b

fold
    :: forall a n c x
    .  Arithmetic a
    => x ~ ArithmeticCircuit a (Vector n)
    => P.Eq c
    => Scale a c
    => Scale a a
    => AdditiveGroup c
    => RandomOracle a a
    => RandomOracle c a
    => RandomOracle [c] a
    => HomomorphicCommit a [a] c
    => HomomorphicCommit a [Map Natural a] c
    => KnownNat n
    => (Vector n (FieldElement x) -> Vector n (FieldElement x))  -- ^ An arithmetisable function to be applied recursively
    -> Natural                             -- ^ The number of iterations to perform
    -> SPS.Input a (RecursiveCircuit n a)  -- ^ Input for the first iteration
    -> FoldResult n c a
fold f iter i = foldN iter ck rc i [] initialAccumulator (Acc.KeyScale one one)
    where
        rc :: RecursiveCircuit n a
        rc = RecursiveCircuit iter (compile @a f)

        initE = hcommit ck $ replicate (SPS.outputLength @a rc) (zero :: a)

        ck = oracle i

        initialAccumulator :: Accumulator (Vector n a) a c (Map Natural a)
        initialAccumulator = Accumulator (AccumulatorInstance (P.pure zero) [hcommit ck [zero :: Map Natural a]] [] initE zero) [zero]


instanceProof
    :: forall n c a
    .  Arithmetic a
    => KnownNat n
    => Scale a a
    => HomomorphicCommit a [Map Natural a] c
    => a
    -> RecursiveCircuit n a
    -> SPS.Input a (RecursiveCircuit n a)
    -> InstanceProofPair (Vector n a) c (Map Natural a)
instanceProof ck rc i = InstanceProofPair i (NARKProof [hcommit ck [m]] [m])
    where
        m = SPS.prover @a rc M.empty i []

foldN
    :: forall n c a
    .  Arithmetic a
    => P.Eq c
    => AdditiveGroup c
    => Scale a c
    => Scale a a
    => KnownNat n
    => RandomOracle a a
    => RandomOracle c a
    => RandomOracle [c] a
    => HomomorphicCommit a [a] c
    => HomomorphicCommit a [Map Natural a] c
    => Natural
    -> a
    -> RecursiveCircuit n a
    -> SPS.Input a (RecursiveCircuit n a)
    -> [P.Bool]
    -> Accumulator (Vector n a) a c (Map Natural a)
    -> Acc.KeyScale a
    -> FoldResult n c a
foldN iter ck rc i verifierResults acc ks
  | iterations rc == 0 = FoldResult i acc (and verifierResults) (Acc.decider (transform ck rc i :: FS_CM n c a) (ck, ks) acc)
  | otherwise = let (output, newAcc, newVerifierResult, newKs) = foldStep ck rc i acc ks
                 in foldN iter ck (rc {iterations = iterations rc -! 1}) output (newVerifierResult : verifierResults) newAcc newKs

executeAc :: forall n a . KnownNat n => RecursiveCircuit n a -> Vector n a -> Vector n a
executeAc (RecursiveCircuit _ rc) i = eval rc i

foldStep
    :: forall n c a
    .  Arithmetic a
    => P.Eq c
    => AdditiveGroup c
    => KnownNat n
    => Scale a c
    => Scale a a
    => RandomOracle a a
    => RandomOracle c a
    => RandomOracle [c] a
    => HomomorphicCommit a [Map Natural a] c
    => HomomorphicCommit a [a] c
    => a
    -> RecursiveCircuit n a
    -> SPS.Input a (RecursiveCircuit n a)
    -> Accumulator (Vector n a) a c (Map Natural a)
    -> Acc.KeyScale a
    -> (SPS.Input a (RecursiveCircuit n a), Accumulator (Vector n a) a c (Map Natural a), P.Bool, Acc.KeyScale a)
foldStep ck rc i acc (Acc.KeyScale alphaSum muSum) = (newInput, newAcc, verifierAccepts, Acc.KeyScale (alphaSum + alphaPows) (muSum + scale (6 :: Natural) alpha))
    where
        fs :: FS_CM n c a
        fs = transform ck rc i

        nark@(InstanceProofPair _ narkProof) = instanceProof ck rc i
        (newAcc, accProof) = Acc.prover fs ck acc nark

        alpha :: a
        alpha = oracle (acc^.x, i, narkCommits narkProof, accProof)

        alphaPows = sum $ P.take (P.length accProof) $ (alpha ^) <$> [1 :: Natural ..]

        verifierAccepts = Acc.verifier @_ @_ @_ @(Map Natural a) @(FS_CM n c a) i (narkCommits narkProof) (acc^.x) (newAcc^.x) accProof
        newInput = executeAc rc i

