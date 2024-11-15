{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.SpecialSound where

import           Data.Functor.Rep                            (Representable (..))
import           Data.Map.Strict                             (elems)
import           Prelude                                     (($))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector                     (Vector)
import qualified ZkFold.Base.Protocol.Protostar.AlgebraicMap as AM
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
class SpecialSoundProtocol f i m c d k a where
      type VerifierOutput f i m c d k a

      prover :: a
        -> i f                          -- ^ public input
        -> f                            -- ^ current random challenge
        -> Natural                      -- ^ round number (starting from 1)
        -> m                            -- ^ prover message

      verifier :: a
        -> i f                          -- ^ public input
        -> Vector k m                   -- ^ prover messages
        -> Vector (k-1) f               -- ^ random challenges
        -> VerifierOutput f i m c d k a -- ^ verifier output

instance (Arithmetic a, Representable i, KnownNat (d + 1)) => SpecialSoundProtocol a i [a] c d 1 (ArithmeticCircuit a i o) where
    type VerifierOutput a i [a] c d 1 (ArithmeticCircuit a i o) = [a]

    -- Just return the witness values on the public input
    prover ac pi _ _ = elems $ witnessGenerator ac pi

    -- | Evaluate the algebraic map on public inputs and prover messages and compare it to a list of zeros
    --
    verifier ac pi pm ts = AM.algebraicMap @_ @_ @d ac pi pm ts one
