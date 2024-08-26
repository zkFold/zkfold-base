{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.ARK.Protostar.ArithmeticCircuit where


import           Control.DeepSeq                                      (NFData)
import           Control.Lens                                         ((^.))
import           Data.List                                            (foldl')
import           Data.Map.Strict                                      (Map, (!))
import qualified Data.Map.Strict                                      as M
import           GHC.Generics                                         (Generic)
import           Prelude                                              (and, otherwise, type (~), ($), (<$>), (<=), (==), (<>))
import qualified Prelude                                              as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Algebra.Polynomials.Multivariate         as PM
import           ZkFold.Base.Algebra.Polynomials.Multivariate
import qualified ZkFold.Base.Data.Vector                              as V
import           ZkFold.Base.Data.Vector                              (Vector)
import           ZkFold.Base.Protocol.ARK.Protostar.Accumulator
import qualified ZkFold.Base.Protocol.ARK.Protostar.AccumulatorScheme as Acc
import           ZkFold.Base.Protocol.ARK.Protostar.Commit
import           ZkFold.Base.Protocol.ARK.Protostar.CommitOpen
import           ZkFold.Base.Protocol.ARK.Protostar.FiatShamir
import           ZkFold.Base.Protocol.ARK.Protostar.Oracle
import qualified ZkFold.Base.Protocol.ARK.Protostar.SpecialSound      as SPS
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.FieldElement                    (FieldElement)


{--

1. Compress verification checks (Section 3.5; )
2. Commit (Section 3.2; ZkFold.Base.Protocol.ARK.Protostar.CommitOpen)
3. Fiat-Shamir transform (Section 3.3; ZkFold.Base.Protocol.ARK.Protostar.FiatShamir)
   A technique for taking an interactive proof of knowledge and creating a digital signature based on it.
   This way, some fact (for example, knowledge of a certain secret number) can be publicly proven without revealing underlying information.
4. Accumulation scheme (Section 3.4; ZkFold.Base.Protocol.ARK.Protostar.AccumulatorScheme)
5. Obtain the IVC scheme (Theorem 1 from “Proof-Carrying Data Without Succinct Arguments”; )

--}


-- | A data for recurcive computations.
-- @circuit@ is an Arithmetic circuit with @n@ inputs and @n@ outputs applied to itself (i.e. outputs are fed as inputs at the next iteration) @iterations@ times.
--
data RecursiveCircuit n a
    = RecursiveCircuit
        { iterations :: Natural
        , circuit    :: ArithmeticCircuit a (Vector n)
        } deriving (Generic, NFData)

instance (KnownNat n, Arithmetic a) => SPS.SpecialSoundProtocol a (RecursiveCircuit n a) where
    type Witness a (RecursiveCircuit n a) = Map Natural a
    type Input a (RecursiveCircuit n a) = Vector n a
    type ProverMessage t (RecursiveCircuit n a) = a
    type VerifierMessage t (RecursiveCircuit n a) = a
    type Degree (RecursiveCircuit n a) = 2

    -- One round for Plonk
    rounds = P.const 1

    outputLength (RecursiveCircuit _ ac) = P.fromIntegral $ M.size $ acSystem ac

    -- The transcript will be empty at this point, it is a one-round protocol
    --
    prover rc@(RecursiveCircuit _ ac) _ i _ = oracle $ witnessGenerator ac (M.fromList $ P.zip [1..] (V.fromVector i))

    -- We can modify the polynomial system from the circuit.
    -- The result is a system of @n+1@-variate polynomials
    -- where variables @0@ to @n-1@ are inputs and variable @n@ is hash of the prover message
    --
    algebraicMap rc@(RecursiveCircuit _ ac) i pm _ = proverPoly : P.fmap remapPoly sys
        where
            proverPoly :: Poly a Natural Natural
            proverPoly = var n - constant (P.head pm)

            n :: Natural
            n = value @n

            witness = witnessGenerator ac (M.fromList $ P.zip [1..] (V.fromVector i))

            sys :: [Poly a Natural Natural]
            sys = M.elems $ acSystem (circuit rc)

            -- Substitutes all non-input variab;es with their actual values.
            -- Decreases indices of input variables by one
            --
            remap :: (a, Map Natural Natural) -> (a, Map Natural Natural)
            remap (coeff, vars) =
                foldl'
                    (\(cf, m) (v, p) -> if v <= n then (cf, M.insert (v -! 1) p m) else (cf * fromConstant ((witness ! v)^p), m))
                    (coeff, M.empty)
                    (M.toList vars)

            remapMono :: (a, Mono Natural Natural) -> (a, Mono Natural Natural)
            remapMono (coeff, M vars) =
                let (newCoeff, newVars) = remap (coeff, vars)
                 in (newCoeff, M newVars)

            remapPoly :: Poly a Natural Natural -> Poly a Natural Natural
            remapPoly (P monos) = P (remapMono <$> monos)

    -- | Evaluate the algebraic map on public inputs and prover messages and compare it to a list of zeros
    --
    verifier rc i pm ts = P.fmap (PM.evalPolynomial PM.evalMonomial (varMap !)) amap == zeros
        where
            amap = SPS.algebraicMap rc i pm ts
            zeros = P.const zero <$> amap
            varMap = M.fromList $ P.zip [0..] (V.fromVector i <> pm)

data FoldResult n a
    = FoldResult
    { output          :: Vector n a
    , lastAccumulator :: Accumulator (Vector n a) a a a
    , verifierOutput  :: P.Bool
    , deciderOutput   :: P.Bool
    } deriving (P.Show, Generic, NFData)

type FS_CM n a = FiatShamir a (CommitOpen a a (RecursiveCircuit n a))

transform
    :: forall n a
    .  RandomOracle [a] a
    => RecursiveCircuit n a
    -> Vector n a
    -> FS_CM n a
transform rc v = FiatShamir (CommitOpen oracle rc) v

fold
    :: forall a c n
    .  Arithmetic a
    => P.Show a
    => Scale a a
    => RandomOracle a a
    => HomomorphicCommit a [a] a
    => SymbolicData (ArithmeticCircuit a) (FieldElement c)
    => TypeSize (ArithmeticCircuit a) (FieldElement c) ~ 1
    => Support (ArithmeticCircuit a) (FieldElement c) ~ ()
    => KnownNat n
    => (Vector n (FieldElement c) -> Vector n (FieldElement c))  -- ^ An arithmetisable function to be applied recursively
    -> Natural                             -- ^ The number of iterations to perform
    -> SPS.Input a (RecursiveCircuit n a)  -- ^ Input for the first iteration
    -> FoldResult n a
fold f iter i = foldN ck rc i [] initialAccumulator
    where
        rc :: RecursiveCircuit n a
        rc = RecursiveCircuit iter (compile @a f)

        m = oracle $ executeAc rc i

        ck = oracle i

        initialAccumulator :: Accumulator (Vector n a) a a a
        initialAccumulator = Accumulator (AccumulatorInstance i [commit ck [m]] [] zero one) [m]


instanceProof
    :: forall n a
    .  RandomOracle (Vector n a) a
    => RandomOracle a a
    => P.Show a
    => Ring a
    => a
    -> RecursiveCircuit n a
    -> SPS.Input a (RecursiveCircuit n a)
    -> InstanceProofPair (Vector n a) a a
instanceProof ck rc i = InstanceProofPair i (NARKProof [commit ck [m]] [m])
    where
        m = oracle $ executeAc rc i

foldN
    :: forall n a
    .  Arithmetic a
    => P.Show a
    => KnownNat n
    => Scale a a
    => RandomOracle a a
    => HomomorphicCommit a [a] a
    => a
    -> RecursiveCircuit n a
    -> SPS.Input a (RecursiveCircuit n a)
    -> [P.Bool]
    -> Accumulator (Vector n a) a a a
    -> FoldResult n a
foldN ck rc i verifierResults acc
  | iterations rc == 0 = FoldResult i acc (and verifierResults) (Acc.decider (transform rc i) ck acc)
  | otherwise = let (output, newAcc, newVerifierResult) = foldStep ck rc i acc
                 in foldN ck (rc {iterations = iterations rc -! 1}) output (newVerifierResult : verifierResults) newAcc

executeAc :: forall n a . RecursiveCircuit n a -> Vector n a -> Vector n a
executeAc (RecursiveCircuit _ rc) i = eval rc (M.fromList $ P.zip [1..] (V.fromVector i))

foldStep
    :: forall n a
    .  Arithmetic a
    => P.Show a
    => KnownNat n
    => Scale a a
    => RandomOracle a a
    => HomomorphicCommit a [a] a
    => a
    -> RecursiveCircuit n a
    -> SPS.Input a (RecursiveCircuit n a)
    -> Accumulator (Vector n a) a a a
    -> (SPS.Input a (RecursiveCircuit n a), Accumulator (Vector n a) a a a, P.Bool)
foldStep ck rc i acc = (newInput, newAcc, verifierAccepts)
    where
        fs :: FS_CM n a
        fs = transform rc i

        nark@(InstanceProofPair _ narkProof) = instanceProof ck rc i
        (newAcc, accProof) = Acc.prover fs ck acc nark
        verifierAccepts = Acc.verifier @_ @_ @_ @a @(FS_CM n a) i (narkCommits narkProof) (acc^.x) (newAcc^.x) accProof
        newInput = executeAc rc i
