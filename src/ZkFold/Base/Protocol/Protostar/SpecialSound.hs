{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Base.Protocol.Protostar.SpecialSound where

import           Numeric.Natural (Natural)
import           Prelude         hiding (length)

type SpecialSoundTranscript t a = [(ProverMessage t a, VerifierMessage t a)]

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

      type Degree a :: Natural
      -- ^ d in the paper, the verifier degree

      outputLength :: a -> Natural
      -- ^ l in the paper, the number of algebraic equations checked by the verifier

      rounds :: a -> Natural
      -- ^ k in the paper

      prover :: a -> Witness f a -> Input f a -> SpecialSoundTranscript f a -> ProverMessage f a

      algebraicMap
          :: a
          -> Input f a  -- ^ public input
          -> [ProverMessage f a]  -- ^ NARK proof witness (the list of prover messages)
          -> [f]        -- ^ Verifier random challenges
          -> f          -- ^ Slack variable for padding
          -> [f]
      -- ^ the algebraic map V_sps computed by the verifier.

      verifier :: a -> Input f a -> [ProverMessage f a] -> [f] -> Bool
