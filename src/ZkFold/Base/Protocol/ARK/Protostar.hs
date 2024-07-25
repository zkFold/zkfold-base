{-# LANGUAGE DeriveAnyClass #-}

module ZkFold.Base.Protocol.ARK.Protostar where


import           Control.DeepSeq                                     (NFData)
import           Data.Map.Strict                                     (Map)
import qualified Data.Map.Strict                                     as M
import           GHC.Generics                                        (Generic)
import           Prelude                                             (($))
import qualified Prelude                                             as P

import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Data.Vector                             as V
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
        , circuit    :: ArithmeticCircuit a (Vector n)
        } deriving (Generic, NFData)

instance Arithmetic a => SpecialSoundProtocol a (RecursiveCircuit n a) where
    type Witness a (RecursiveCircuit n a) = Map Natural a 
    type Input a (RecursiveCircuit n a) = Vector n a
    type ProverMessage a (RecursiveCircuit n a) = Vector n a
    type VerifierMessage a (RecursiveCircuit n a) = Vector n a
    type Degree (RecursiveCircuit n a) = 2

    rounds = iterations

    outputLength (RecursiveCircuit _ c) = P.fromIntegral $ M.size $ constraintSystem c

    prover rc w i ts = eval (circuit rc) (M.fromList $ P.zip [1..] (V.fromVector i))

    algebraicMap rc i pm vm = M.elems $ constraintSystem (circuit rc) 

    verifier rc i pm vm = P.undefined

