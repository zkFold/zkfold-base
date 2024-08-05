{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TypeOperators  #-}

module ZkFold.Base.Protocol.ARK.Protostar.ArithmeticCircuit where


import           Control.DeepSeq                                        (NFData)
import           Data.Map.Strict                                        (Map)
import qualified Data.Map.Strict                                        as M
import           GHC.Generics                                           (Generic)
import           Prelude                                                (type (~), ($), (==))
import qualified Prelude                                                as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import qualified ZkFold.Base.Data.Vector                                as V
import           ZkFold.Base.Data.Vector                                (Vector)
import           ZkFold.Base.Protocol.ARK.Protostar.Accumulator
import qualified ZkFold.Base.Protocol.ARK.Protostar.AccumulatorScheme   as Acc
import qualified ZkFold.Base.Protocol.ARK.Protostar.SpecialSound        as SPS
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Data.Conditional
import qualified ZkFold.Symbolic.Data.Eq                                as Eq
import           ZkFold.Symbolic.Data.FieldElement                      (FieldElement)


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

instance Arithmetic a => SPS.SpecialSoundProtocol a (RecursiveCircuit n a) where
    type Witness a (RecursiveCircuit n a) = Map Natural a
    type Input a (RecursiveCircuit n a) = Vector n a
    type ProverMessage a (RecursiveCircuit n a) = Vector n a
    type VerifierMessage a (RecursiveCircuit n a) = Vector n a
    type Degree (RecursiveCircuit n a) = 2

    -- One round for Plonk
    rounds = P.const 1

    outputLength (RecursiveCircuit _ ac) = P.fromIntegral $ M.size $ acSystem ac

    -- The transcript will be empty at this point, it is a one-round protocol
    --
    prover rc _ i _ = eval (circuit rc) (M.fromList $ P.zip [1..] (V.fromVector i))

    -- We can use the polynomial system from the circuit, no need to build it from scratch
    --
    algebraicMap rc _ _ _ = M.elems $ acSystem (circuit rc)

    -- The transcript is only one prover message since this is a one-round protocol
    --
    verifier rc i pm _ = eval (circuit rc) (M.fromList $ P.zip [1..] (V.fromVector i)) == P.head pm

data FoldResult n a
    = FoldResult
    { output          :: Vector n a
    , lastAccumulator :: Accumulator a a a
    , verifierOutput  :: P.Bool
    , deciderOutput   :: P.Bool
    }

fold
    :: forall a x n
    .  SymbolicData (ArithmeticCircuit a) x
    => TypeSize (ArithmeticCircuit a) x ~ n
    => KnownNat n
    => Support (ArithmeticCircuit a) x ~ ()
    => P.Eq a
    => MultiplicativeMonoid a
    => (x -> x)  -- ^ An arithmetisable function to be applied recursively
    -> Natural   -- ^ The number of iterations to perform
    -> SPS.Input a (RecursiveCircuit n a)  -- ^ Input for the first iteration
    -> FoldResult n a
fold f iter i = foldN rc i [] initialAccumulator
    where
        rc :: RecursiveCircuit n a
        rc = RecursiveCircuit iter (compile @a f)

        initialAccumulator :: Accumulator a a a
        initialAccumulator = Accumulator ((oracle i) [{- TODO add C_0-}] [] zero one) (oracle [{- TODO add witness-}])


instanceProof :: RecursiveCircuit n a -> SPS.Input a (RecursiveCircuit n a) -> InstanceProofPair a a a
instanceProof rc i = undefined

foldN :: RecursiveCircuit n a -> SPS.Input a (RecursiveCircuit n a) -> [P.Bool] -> Accumulator a a a -> FoldResult n a
foldN rc i verifierResults acc
  | iterations rc == 0 = FoldResult i acc (and verifierResults) (decider rc acc)
  | otherwise = let (output, newAcc, newVerifierResult) = foldStep rc i acc
                 in foldN (rc {iterations = iterations rc -! 1}) output (newVerifierResult : verifierResults) newAcc

foldStep :: RecursiveCircuit n a -> SPS.Input a (RecursiveCircuit n a) -> Accumulator a a a -> (SPS.Input a (RecursiveCircuit n a), Accumulator a a a, P.Bool)
foldStep rc i acc = (newInput, newAcc, verifierAccepts)
    where
        nark@(InstanceProofPair _ narkProof) = instanceProof rc i
        (newAcc, accProof) = prove rc acc nark
        verifierAccepts = verify (narkCommits narkProof) acc newAcc accProof
        newInput = eval (circuit rc) (M.fromList $ P.zip [1..] (V.fromVector i))
