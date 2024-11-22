{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.SpecialSound where

import           Data.Functor.Rep                            (Representable (..))
import           Data.Map.Strict                             (elems)
import           GHC.Generics                                (U1(..), (:*:)(..))
import           Prelude                                     (($), undefined)

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
class SpecialSoundProtocol f i p m c d k a where
  type VerifierOutput f i p m c d k a

  input :: a
    -> i f                          -- ^ previous public input
    -> p f                          -- ^ witness
    -> i f                          -- ^ public input

  prover :: a
    -> i f                          -- ^ previous public input
    -> p f                          -- ^ witness
    -> f                            -- ^ current random challenge
    -> Natural                      -- ^ round number (starting from 1)
    -> m                            -- ^ prover message

  verifier :: a
    -> i f                          -- ^ public input
    -> Vector k m                   -- ^ prover messages
    -> Vector (k-1) f               -- ^ random challenges
    -> VerifierOutput f i p m c d k a -- ^ verifier output

data ArithmetizableFunction a i p = ArithmetizableFunction 
  { afEval    :: i a -> p a -> i a
  , afCircuit :: ArithmeticCircuit a (i :*: p) i U1
  }

instance (Arithmetic a, Representable i, Representable p, KnownNat (d + 1))
    => SpecialSoundProtocol a i p [a] c d 1 (ArithmetizableFunction a i p) where
  type VerifierOutput a i p [a] c d 1 (ArithmetizableFunction a i p) = [a]

  input ArithmetizableFunction {..} = afEval

  -- | Just return the witness values on the previous public input
  prover ArithmetizableFunction {..} pi0 w _ _ = elems $ witnessGenerator afCircuit (pi0 :*: w) undefined

  -- | Evaluate the algebraic map on public inputs and prover messages
  --
  verifier ArithmetizableFunction {..} pi pm ts = AM.algebraicMap @_ @_ @d afCircuit pi pm ts one
