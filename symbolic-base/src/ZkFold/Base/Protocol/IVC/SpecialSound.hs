{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.IVC.SpecialSound where

import           Data.Function                         (($))
import           Data.Functor.Rep                      (Representable (..))
import           Data.Map.Strict                       (elems)
import           GHC.Generics                          ((:*:) (..))
import           Prelude                               (Ord)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector               (Vector)
import           ZkFold.Base.Protocol.IVC.AlgebraicMap
import           ZkFold.Base.Protocol.IVC.Predicate    (Predicate (..), PredicateFunctionAssumptions)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.MonadCircuit          (ResidueField)

{-- | Section 3.1

The protocol Πsps has 3 essential parameters k, d, l ∈ N, meaning that Πsps is a (2k − 1)-
move protocol with verifier degree d and output length l (i.e. the verifier checks l degree
d algebraic equations). In each round i (1 ≤ i ≤ k), the prover Psps(pi, w, [mj , rj], j=1 to i-1)
generates the next message mi on input the public input pi, the witness w, and the current
transcript [mj , rj], j=1 to i-1, and sends mi to the verifier; the verifier replies with a random
challenge ri ∈ F. After the final message mk, the verifier computes the algebraic map Vsps
and checks that the output is a zero vector of length l.

--}

data SpecialSoundProtocol k a i p = SpecialSoundProtocol
  {
    input :: forall f . PredicateFunctionAssumptions a f
      => i f                            -- ^ previous public input
      -> p f                            -- ^ witness
      -> i f                            -- ^ public input

  , prover :: forall f . (PredicateFunctionAssumptions a f, ResidueField f)
      => i f                            -- ^ previous public input
      -> p f                            -- ^ witness
      -> f                              -- ^ current random challenge
      -> Natural                        -- ^ round number (starting from 1)
      -> [f]                            -- ^ prover message

  , verifier :: forall f . PredicateFunctionAssumptions a f
      => i f                            -- ^ public input
      -> Vector k [f]                   -- ^ prover messages
      -> Vector (k-1) f                 -- ^ random challenges
      -> [f]                            -- ^ verifier output
  }

specialSoundProtocol :: forall d a i p .
    ( KnownNat (d+1)
    , Representable i
    , Ord (Rep i)
    , Representable p
    ) => Predicate a i p -> SpecialSoundProtocol 1 a i p
specialSoundProtocol phi@Predicate {..} =
  let
      prover :: forall f . (PredicateFunctionAssumptions a f, ResidueField f) => i f -> p f -> f -> Natural -> [f]
      prover pi0 w _ _ = elems $ witnessGenerator' @f predicateCircuit (pi0 :*: w) (predicateFunction pi0 w)

      verifier :: forall f . PredicateFunctionAssumptions a f => i f -> Vector 1 [f] -> Vector 0 f -> [f]
      verifier pi pm ts = algebraicMap @d phi pi pm ts one
  in
      SpecialSoundProtocol predicateFunction prover verifier
