{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.SpecialSound where

import           Data.Functor.Rep                            (Representable(..))
import           Data.Map.Strict                             (elems)
import qualified Data.Map.Strict                             as M
import           Prelude                                     (($))
import qualified Prelude                                     as P

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
class SpecialSoundProtocol f pi m k a where
      type VerifierOutput f pi m k a

      outputLength :: a -> Natural
      -- ^ l in the paper, the number of algebraic equations checked by the verifier

      prover :: a
        -> pi                    -- ^ public input
        -> f    -- ^ current random challenge
        -> Natural               -- ^ round number (starting from 0)
        -> m

      verifier :: a
        -> pi                           -- ^ public input
        -> Vector k m                   -- ^ prover messages
        -> Vector (k-1) f -- ^ random challenges
        -> VerifierOutput f pi m k a    -- ^ verifier output

type BasicSpecialSoundProtocol f pi m k a =
  ( SpecialSoundProtocol f pi m k a
  , KnownNat k
  )

instance (Representable i, Arithmetic a, AdditiveGroup (i a), Scale a (i a))
      => SpecialSoundProtocol a (i a) [a] 1 (ArithmeticCircuit a i o) where
    type VerifierOutput a (i a) [a] 1 (ArithmeticCircuit a i o)  = [a]

    outputLength ac = P.fromIntegral $ M.size (acSystem ac)

    -- Just return the witness values on the public input
    prover ac pi _ _ = elems $ witnessGenerator ac pi

    -- | Evaluate the algebraic map on public inputs and prover messages and compare it to a list of zeros
    --
    verifier ac pi pm ts = AM.algebraicMap ac pi pm ts one
