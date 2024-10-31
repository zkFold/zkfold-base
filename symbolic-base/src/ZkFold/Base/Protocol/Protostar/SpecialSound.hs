{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Base.Protocol.Protostar.SpecialSound where

import           Numeric.Natural (Natural)
import           Prelude         hiding (length)

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

      type Degree a :: Natural
      -- ^ d in the paper, the verifier degree

      outputLength :: a -> Natural
      -- ^ l in the paper, the number of algebraic equations checked by the verifier

      rounds :: a -> Natural
      -- ^ k in the paper

      prover :: a
        -> Witness f a        -- ^ witness
        -> Input f a          -- ^ public input
        -> f                  -- ^ current random challenge
        -> Natural            -- ^ round number (starting from 0)
        -> ProverMessage f a

      verifier :: a
        -> Input f a           -- ^ public input
        -> [ProverMessage f a] -- ^ prover messages
        -> [f]                 -- ^ random challenges
        -> VerifierOutput f a  -- ^ verifier output

-- | Algebraic map is a much more versatile and powerful tool when used separatey from SpecialSoundProtocol.
-- It calculates a system of equations @[f]@ defining @a@ in some way.
-- If @f@ is a number or a field element, then the result is a vector of polynomial values.
-- However, @f@ can be a polynomial, in which case the result will be a system of polynomials.
-- This polymorphism is exploited in the AccumulatorScheme prover.
--
class AlgebraicMap f a where
    type MapInput f a
    type MapMessage f a

    -- | the algebraic map V_sps computed by the verifier.
    algebraicMap :: a
        -> MapInput f a     -- ^ public input
        -> [MapMessage f a] -- ^ NARK proof witness (the list of prover messages)
        -> [f]              -- ^ Verifier random challenges
        -> f                -- ^ Slack variable for padding
        -> [f]
