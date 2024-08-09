{-# LANGUAGE DeriveAnyClass #-}

module ZkFold.Base.Protocol.ARK.Protostar where


import           Control.DeepSeq                                     (NFData)
import           Data.Map.Strict                                     (Map)
import qualified Data.Map.Strict                                     as M
import           GHC.Generics                                        (Generic)
import           Prelude                                             (($), (==))
import qualified Prelude                                             as P

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.Polynomials.Multivariate        (evalMonomial, evalPolynomial, var)
import           ZkFold.Base.Data.Vector                             (Vector)
import           ZkFold.Base.Protocol.ARK.Protostar.SpecialSound
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

{--

1. Compress verification checks (Section 3.5; )
2. Commit (Section 3.2; ZkFold.Base.Protocol.ARK.Protostar.CommitOpen)
3. Fiat-Shamir transform (Section 3.3; ZkFold.Base.Protocol.ARK.Protostar.FiatShamir)
   A technique for taking an interactive proof of knowledge and creating a digital signature based on it.
   This way, some fact (for example, knowledge of a certain secret number) can be publicly proven without revealing underlying information.
4. Accumulation scheme (Section 3.4; ZkFold.Base.Protocol.ARK.Protostar.AccumulatorScheme)
5. Obtain the IVC scheme (Theorem 1 from “Proof-Carrying Data Without Succinct Arguments”; )

--}
--
--
-- To complete the protocol:
-- 1. Finish AccumulatorScheme -- and Lookup
-- 2. Implement IVC scheme
-- 3. Put it all together
-- 4. Input and output == AC


-- | A data for recurcive computations.
-- @circuit@ is an Arithmetic circuit with @n@ inputs and @n@ outputs applied to itself (i.e. outputs are fed as inputs at the next iteration) @iterations@ times.
--
data RecursiveCircuit n a
    = RecursiveCircuit
        { iterations :: Natural
        , circuit    :: ArithmeticCircuit a (Vector n) (Vector n)
        } deriving (Generic, NFData)

instance (Arithmetic a, KnownNat n) => SpecialSoundProtocol a (RecursiveCircuit n a) where
    type Witness a (RecursiveCircuit n a) = Map Natural a
    type Input a (RecursiveCircuit n a) = Vector n a
    type ProverMessage a (RecursiveCircuit n a) = Vector n a
    type VerifierMessage a (RecursiveCircuit n a) = Vector n a
    type Degree (RecursiveCircuit n a) = 2

    -- One round for Plonk
    rounds = P.const 1

    outputLength (RecursiveCircuit _ c) = P.fromIntegral $ M.size $ acSystem c

    -- The transcript will be empty at this point, it is a one-round protocol
    --
    prover rc _ i _ = eval (circuit rc) i

    -- We can use the polynomial system from the circuit, no need to build it from scratch
    --
    algebraicMap rc _ _ _ =
        let
            varF (NewVar ix) = var (ix P.+ value @n)
            varF (InVar ix)  = var (P.fromIntegral ix)
        in
            [ evalPolynomial evalMonomial varF poly
            | poly <- M.elems $ acSystem (circuit rc)
            ]

    -- The transcript is only one prover message since this is a one-round protocol
    --
    verifier rc i pm _ = eval (circuit rc) i == P.head pm

