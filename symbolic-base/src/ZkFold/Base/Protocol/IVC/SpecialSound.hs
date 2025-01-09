{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.IVC.SpecialSound where

import           Data.Functor.Rep                      (Representable (..))
import           Data.Map.Strict                       (elems)
import           GHC.Generics                          ((:*:) (..))
import           Prelude                               (($), Ord)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector               (Vector)
import           ZkFold.Base.Protocol.IVC.AlgebraicMap
import           ZkFold.Base.Protocol.IVC.Predicate    (Predicate (..))
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.FieldElement     (FieldElement)

{-- | Section 3.1

The protocol Πsps has 3 essential parameters k, d, l ∈ N, meaning that Πsps is a (2k − 1)-
move protocol with verifier degree d and output length l (i.e. the verifier checks l degree
d algebraic equations). In each round i (1 ≤ i ≤ k), the prover Psps(pi, w, [mj , rj], j=1 to i-1)
generates the next message mi on input the public input pi, the witness w, and the current
transcript [mj , rj], j=1 to i-1, and sends mi to the verifier; the verifier replies with a random
challenge ri ∈ F. After the final message mk, the verifier computes the algebraic map Vsps
and checks that the output is a zero vector of length l.

--}

data SpecialSoundProtocol k i p ctx = SpecialSoundProtocol
  {
    input ::
         i (WitnessField ctx)                            -- ^ previous public input
      -> p (WitnessField ctx)                            -- ^ witness
      -> i (WitnessField ctx)                            -- ^ public input

  , prover ::
         i (WitnessField ctx)                            -- ^ previous public input
      -> p (WitnessField ctx)                            -- ^ witness
      -> WitnessField ctx                                -- ^ current random challenge
      -> Natural                                         -- ^ round number (starting from 1)
      -> [WitnessField ctx]                              -- ^ prover message

  , verifier ::
         i (FieldElement ctx)                            -- ^ public input
      -> Vector k [FieldElement ctx]                     -- ^ prover messages
      -> Vector (k-1) (FieldElement ctx)                 -- ^ random challenges
      -> [FieldElement ctx]                              -- ^ verifier output
  }

specialSoundProtocol :: forall d i p ctx .
    ( KnownNat (d+1)
    , Representable i
    , Ord (Rep i)
    , Representable p
    , Symbolic ctx
    , FromConstant (BaseField ctx) (WitnessField ctx)
    , Scale (BaseField ctx) (WitnessField ctx)
    ) => Predicate i p ctx -> SpecialSoundProtocol 1 i p ctx
specialSoundProtocol phi@Predicate {..} =
  let
      prover pi0 w _ _ = elems $ witnessGenerator @(WitnessField ctx) predicateCircuit (pi0 :*: w) (predicateWitness pi0 w)

      verifier pi pm ts = algebraicMap @d phi pi pm ts one
  in
      SpecialSoundProtocol predicateWitness prover verifier
