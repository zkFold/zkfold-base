{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.SpecialSound where

import           Data.Map.Strict                             (elems)
import qualified Data.Map.Strict                             as M
import           Prelude                                     (($))
import qualified Prelude                                     as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import qualified ZkFold.Base.Protocol.Protostar.AlgebraicMap as AM
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler

{-- | Section 3.1

The protocol Πsps has 3 essential parameters k, d, l ∈ N, meaning that Πsps is a (2k − 1)-
move protocol with verifier degree d and output length l (i.e. the verifier checks l degree
d algebraic equations). In each round i (1 ≤ i ≤ k), the prover Psps(pi, w, [mj , rj], j=1 to i-1)
generates the next message mi on input the public input pi, the witness w, and the current
transcript [mj , rj], j=1 to i-1, and sends mi to the verifier; the verifier replies with a random
challenge ri ∈ F. After the final message mk, the verifier computes the algebraic map Vsps
and checks that the output is a zero vector of length l.

--}
class SpecialSoundProtocol f a where
      type Witness f a
      type Input f a
      type ProverMessage f a
      type VerifierMessage f a
      type VerifierOutput f a

      outputLength :: a -> Natural
      -- ^ l in the paper, the number of algebraic equations checked by the verifier

      rounds :: a -> Natural
      -- ^ k in the paper

      prover :: a
        -> Witness f a         -- ^ witness
        -> Input f a           -- ^ public input
        -> VerifierMessage f a -- ^ current random challenge
        -> Natural             -- ^ round number (starting from 0)
        -> ProverMessage f a

      verifier :: a
        -> Input f a             -- ^ public input
        -> [ProverMessage f a]   -- ^ prover messages
        -> [VerifierMessage f a] -- ^ random challenges
        -> VerifierOutput f a    -- ^ verifier output

instance (KnownNat n, Arithmetic a) => SpecialSoundProtocol a (ArithmeticCircuit a (Vector n) o) where

    type Witness a (ArithmeticCircuit a (Vector n) o) = ()
    type Input a (ArithmeticCircuit a (Vector n) o) = Vector n a
    type ProverMessage a (ArithmeticCircuit a (Vector n) o) = [a]
    type VerifierMessage a (ArithmeticCircuit a (Vector n) o) = a
    type VerifierOutput a (ArithmeticCircuit a (Vector n) o)  = [a]
    -- type Degree (ArithmeticCircuit a (Vector n) o) = AM.Degree (ArithmeticCircuit a (Vector n) o)

    -- One round for Plonk
    rounds = P.const 1

    outputLength ac = P.fromIntegral $ M.size (acSystem ac)

    -- The transcript will be empty at this point, it is a one-round protocol.
    -- Input is arithmetised. We need to combine its witness with the circuit's witness.
    --
    prover ac _ pi _ _ = elems $ witnessGenerator ac pi

    -- | Evaluate the algebraic map on public inputs and prover messages and compare it to a list of zeros
    --
    verifier rc i pm ts = AM.algebraicMap rc i pm ts one