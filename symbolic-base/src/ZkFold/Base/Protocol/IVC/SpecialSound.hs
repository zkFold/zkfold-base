{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.IVC.SpecialSound where

import           Data.Binary                           (Binary)
import           Data.Function                         (($))
import           Data.Functor.Rep                      (Representable (..))
import           Data.Map.Strict                       (elems)
import           GHC.Generics                          ((:*:) (..))
import           Prelude                               (undefined)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector               (Vector)
import qualified ZkFold.Base.Protocol.IVC.AlgebraicMap as AM
import           ZkFold.Base.Protocol.IVC.Predicate    (Predicate (..))
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

data SpecialSoundProtocol k i p m o f = SpecialSoundProtocol
  {
    input ::
         i f                            -- ^ previous public input
      -> p f                            -- ^ witness
      -> i f                            -- ^ public input

  , prover ::
         i f                            -- ^ previous public input
      -> p f                            -- ^ witness
      -> f                              -- ^ current random challenge
      -> Natural                        -- ^ round number (starting from 1)
      -> m                              -- ^ prover message

  , verifier ::
         i f                            -- ^ public input
      -> Vector k m                     -- ^ prover messages
      -> Vector (k-1) f                 -- ^ random challenges
      -> o                              -- ^ verifier output
  }

specialSoundProtocol :: forall d a i p .
    ( KnownNat (d+1)
    , Arithmetic a
    , Binary a
    , Representable i
    , Representable p
    ) => Predicate a i p -> SpecialSoundProtocol 1 i p [a] [a] a
specialSoundProtocol phi@Predicate {..} =
  let
      prover pi0 w _ _ = elems $ witnessGenerator predicateCircuit (pi0 :*: w) (predicateEval pi0 w)
      verifier pi pm ts = AM.algebraicMap @d phi pi pm ts one
  in
      SpecialSoundProtocol predicateEval prover verifier

specialSoundProtocol' :: forall d a i p f .
    ( KnownNat (d+1)
    , Representable i
    , Ring f
    , Scale a f
    ) => Predicate a i p -> SpecialSoundProtocol 1 i p [f] [f] f
specialSoundProtocol' phi =
  let
      verifier pi pm ts = AM.algebraicMap @d phi pi pm ts one
  in
      SpecialSoundProtocol undefined undefined verifier

