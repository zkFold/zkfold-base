{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.IVC.FiatShamir where

import           Data.Constraint                       (withDict)
import           Data.Constraint.Nat                   (plusMinusInverse1)
import           Prelude                               hiding (Bool (..), Eq (..), init, length, pi, scanl, unzip)

import           ZkFold.Base.Algebra.Basic.Class       (Ring)
import           ZkFold.Base.Algebra.Basic.Number      (KnownNat, type (-))
import           ZkFold.Base.Data.Vector               (Vector, init, scanl, unfold)
import           ZkFold.Base.Protocol.IVC.CommitOpen
import           ZkFold.Base.Protocol.IVC.Oracle       (HashAlgorithm, oracle)
import           ZkFold.Symbolic.Class                 (Symbolic(..))
import           ZkFold.Symbolic.Data.FieldElement     (FieldElement)

-- type FiatShamir k i p c m o f = SpecialSoundProtocol 1 i p (Vector k (m, c f)) (Vector k (c f), o) f

data FiatShamir k i p c ctx = FiatShamir
    {
        input   ::
               i (WitnessField ctx)
            -> p (WitnessField ctx)
            -> i (WitnessField ctx)

      , prover  ::
               i (WitnessField ctx)
            -> p (WitnessField ctx)
            -> Vector k ([WitnessField ctx], c (WitnessField ctx))

      , verifier ::
               i (FieldElement ctx)
            -> Vector k ([FieldElement ctx], c (FieldElement ctx))
            -> ([FieldElement ctx], Vector k (c (FieldElement ctx)))
    }

-- The transcript of the Fiat-Shamired protocol (ignoring the last round)
transcript :: forall algo k c f .
    ( HashAlgorithm algo
    , Ring f
    , Foldable c
    ) => f -> Vector k (c f) -> Vector (k-1) f
transcript r0 cs = withDict (plusMinusInverse1 @1 @k) $ init $ init $ scanl (curry (oracle @algo)) r0 cs

fiatShamir :: forall algo k i p c ctx .
    ( HashAlgorithm algo
    , KnownNat k
    , Foldable i
    , Foldable c
    , Symbolic ctx
    ) => CommitOpen k i p c ctx -> FiatShamir k i p c ctx
fiatShamir CommitOpen {..} =
    let
        prover' pi0 w =
            let r0 = oracle @algo pi0
                f (r, k) =
                    let (m', c') = prover pi0 w r k
                    in ((m', c'), (oracle @algo (r, c'), k + 1))
            in unfold f (r0, 1)

        verifier' pi pms =
            let r0 = oracle @algo pi
                rs = transcript @algo r0 $ fmap snd pms
            in verifier pi pms rs
    in
        FiatShamir input prover' verifier'
