{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.Fold where


import           Control.DeepSeq                                     (NFData)
import           Control.Lens                                        ((^.))
import           Data.List                                           (foldl')
import           Data.Map.Strict                                     (Map, (!))
import qualified Data.Map.Strict                                     as M
import           Debug.Trace
import           GHC.Generics                                        (Generic)
import           Prelude                                             (and, otherwise, type (~), ($), (<$>), (<), (<=),
                                                                      (<>), (==))
import qualified Prelude                                             as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Algebra.Polynomials.Multivariate        as PM
import           ZkFold.Base.Algebra.Polynomials.Multivariate
import qualified ZkFold.Base.Data.Vector                             as V
import           ZkFold.Base.Data.Vector                             (Vector)
import           ZkFold.Base.Protocol.Protostar.Accumulator
import           ZkFold.Base.Protocol.Protostar.ArithmeticCircuit
import qualified ZkFold.Base.Protocol.Protostar.AccumulatorScheme    as Acc
import           ZkFold.Base.Protocol.Protostar.Commit
import           ZkFold.Base.Protocol.Protostar.CommitOpen
import           ZkFold.Base.Protocol.Protostar.FiatShamir
import           ZkFold.Base.Protocol.Protostar.Oracle
import qualified ZkFold.Base.Protocol.Protostar.SpecialSound         as SPS
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Data.FieldElement                   (FieldElement)

fact
    :: forall a n c
    .  Arithmetic a
    => c ~ ArithmeticCircuit a (Vector n)
    => KnownNat n
    => MultiplicativeSemigroup (FieldElement c)
    => Vector n (FieldElement c) -> Vector n (FieldElement c)
fact v = V.generate (\i -> if i == 0 then v V.!! 0 * v V.!! 1 else v V.!! 0)

data FoldResult n c a
    = FoldResult
    { output          :: Vector n a
    , lastAccumulator :: Accumulator (Vector n a) a c a
    , verifierOutput  :: P.Bool
    , deciderOutput   :: P.Bool
    } deriving (P.Show, Generic, NFData)

type FS_CM n c a = FiatShamir a (CommitOpen a c (RecursiveCircuit n a))

transform
    :: forall n c a
    .  HomomorphicCommit a [a] c
    => a
    -> RecursiveCircuit n a
    -> Vector n a
    -> FS_CM n c a
transform ck rc v = FiatShamir (CommitOpen (hcommit ck) rc) v

fold
    :: forall a n c x
    .  Arithmetic a
    => x ~ ArithmeticCircuit a (Vector n)
    => P.Show a
    => P.Eq c
    => P.Show c
    => Scale a c
    => Scale a a
    => AdditiveGroup c
    => RandomOracle c a
    => RandomOracle a a
    => HomomorphicCommit a [a] c
    => KnownNat n
    => (Vector n (FieldElement x) -> Vector n (FieldElement x))  -- ^ An arithmetisable function to be applied recursively
    -> Natural                             -- ^ The number of iterations to perform
    -> SPS.Input a (RecursiveCircuit n a)  -- ^ Input for the first iteration
    -> FoldResult n c a
fold f iter i = foldN iter ck rc i [] initialAccumulator
    where
        rc :: RecursiveCircuit n a
        rc = RecursiveCircuit iter (compile @a f)

        m = SPS.prover @a rc M.empty i []
        
        amap = SPS.algebraicMap @a rc (P.pure zero) [zero] []

        e = P.fmap (PM.evalPolynomial PM.evalMonomial (P.const (zero :: a))) amap
        
        initE = hcommit ck e 

        ck = oracle i

        initialAccumulator :: Accumulator (Vector n a) a c a
        initialAccumulator = Accumulator (AccumulatorInstance (P.pure zero) [hcommit ck [zero :: a]] [] initE one) [zero]


instanceProof
    :: forall n c a
    .  Arithmetic a
    => KnownNat n
    => P.Show a
    => HomomorphicCommit a [a] c
    => a
    -> RecursiveCircuit n a
    -> SPS.Input a (RecursiveCircuit n a)
    -> InstanceProofPair (Vector n a) c a
instanceProof ck rc i = InstanceProofPair i (NARKProof [hcommit ck [m]] [m])
    where
        m = SPS.prover @a rc M.empty i []

foldN
    :: forall n c a
    .  Arithmetic a
    => P.Show a
    => P.Eq c
    => P.Show c
    => AdditiveGroup c
    => Scale a c
    => KnownNat n
    => RandomOracle a a
    => RandomOracle c a
    => HomomorphicCommit a [a] c
    => Natural
    -> a
    -> RecursiveCircuit n a
    -> SPS.Input a (RecursiveCircuit n a)
    -> [P.Bool]
    -> Accumulator (Vector n a) a c a
    -> FoldResult n c a
foldN iter ck rc i verifierResults acc
  | iterations rc == 0 = FoldResult i acc (and verifierResults) (Acc.decider (transform ck rc i :: FS_CM n c a) ck acc)
  | otherwise = let (output, newAcc, newVerifierResult) = foldStep ck rc i acc
                 in foldN iter ck (rc {iterations = iterations rc -! 1}) output (newVerifierResult : verifierResults) newAcc

executeAc :: forall n a . KnownNat n => RecursiveCircuit n a -> Vector n a -> Vector n a
executeAc (RecursiveCircuit _ rc) i = eval rc i

foldStep
    :: forall n c a
    .  Arithmetic a
    => P.Show a
    => P.Show c
    => P.Eq c
    => AdditiveGroup c
    => KnownNat n
    => Scale a c
    => RandomOracle a a
    => RandomOracle c a
    => HomomorphicCommit a [a] c
    => a
    -> RecursiveCircuit n a
    -> SPS.Input a (RecursiveCircuit n a)
    -> Accumulator (Vector n a) a c a
    -> (SPS.Input a (RecursiveCircuit n a), Accumulator (Vector n a) a c a, P.Bool)
foldStep ck rc i acc = (newInput, newAcc, verifierAccepts)
    where
        fs :: FS_CM n c a
        fs = transform ck rc i

        nark@(InstanceProofPair _ narkProof) = instanceProof ck rc i
        (newAcc, accProof) = Acc.prover fs ck acc nark
        verifierAccepts = Acc.verifier @_ @_ @_ @a @(FS_CM n c a) i (narkCommits narkProof) (acc^.x) (newAcc^.x) accProof
        newInput = executeAc rc i

