{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Base.Protocol.ARK.Protostar.SpecialSound where

import           Numeric.Natural                              (Natural)
import           Prelude                                      hiding (length)

import           ZkFold.Base.Algebra.Polynomials.Multivariate (Poly)
import           ZkFold.Base.Data.Vector                      (Vector)
import           ZkFold.Symbolic.Compiler.Arithmetizable      (Arithmetic)

type SpecialSoundTranscript t a = [(ProverMessage t a, VerifierMessage t a)]

type LMap l f = Vector l (Poly f Natural Natural)

{-- | Section 3.1

The protocol Πsps has 3 essential parameters k, d, l ∈ N, meaning that Πsps is a (2k − 1)-
move protocol with verifier degree d and output length l (i.e. the verifier checks l degree
d algebraic equations). In each round i (1 ≤ i ≤ k), the prover Psps(pi, w, [mj , rj], j=1 to i-1)
generates the next message mi on input the public input pi, the witness w, and the current
transcript [mj , rj], j=1 to i-1, and sends mi to the verifier; the verifier replies with a random
challenge ri ∈ F. After the final message mk, the verifier computes the algebraic map Vsps
and checks that the output is a zero vector of length l.

--}
class Arithmetic f => SpecialSoundProtocol f a where
      type Witness f a
      type Input f a
      type ProverMessage t a
      type VerifierMessage t a

      type Dimension a :: Natural
      -- ^ l in the paper
      type Degree a :: Natural
      -- ^ d in the paper

      rounds :: a -> Natural
      -- ^ k in the paper

      prover :: a -> Witness f a -> Input f a -> SpecialSoundTranscript f a -> ProverMessage f a

      algebraicMap 
          :: a 
          -> Input f a 
          -> [ProverMessage Natural a] 
          -> [VerifierMessage Natural a] 
          -> LMap (Dimension a) f
      -- ^ the algebraic map V_sps computed by the verifier. 
      -- The j-th element of the vector is a homogeneous degree-j algebraic map that outputs a vector of @Dimension a@ field elements.
      -- Variables have natural indices from @0@ to @2k@:
      -- Variable @0@ is public input
      -- Variables @1@ to @k@ are prover messages from the transcript
      -- Variables @k+1@ to @2k@ are random challenges from the verifier

      verifier :: a -> Input f a -> [ProverMessage f a] -> [VerifierMessage f a] -> Bool

