{-# LANGUAGE TypeOperators #-}

module ZkFold.Base.Protocol.IVC.CommitOpen where

import           Data.Zip                              (zipWith)
import           Prelude                               hiding (Num (..), length, pi, tail, zipWith, (&&))

import           ZkFold.Base.Algebra.Basic.Class       (AdditiveGroup (..))
import           ZkFold.Base.Algebra.Basic.Number      (Natural, type (-))
import           ZkFold.Base.Data.Vector               (Vector)
import           ZkFold.Base.Protocol.IVC.Commit       (HomomorphicCommit (hcommit))
import           ZkFold.Base.Protocol.IVC.SpecialSound (SpecialSoundProtocol (..))
import           ZkFold.Symbolic.Class                 (Symbolic(..))
import           ZkFold.Symbolic.Data.FieldElement     (FieldElement)

data CommitOpen k i p c ctx = CommitOpen
    {
        input   ::
               i (WitnessField ctx)
            -> p (WitnessField ctx)
            -> i (WitnessField ctx)

      , prover  ::
               i (WitnessField ctx)
            -> p (WitnessField ctx)
            -> WitnessField ctx
            -> Natural
            -> ([WitnessField ctx], c (WitnessField ctx))

      , verifier ::
               i (FieldElement ctx)
            -> Vector k ([FieldElement ctx], c (FieldElement ctx))
            -> Vector (k-1) (FieldElement ctx)
            -> ([FieldElement ctx], Vector k (c (FieldElement ctx)))
    }

commitOpen :: forall k i p c ctx .
    ( HomomorphicCommit [WitnessField ctx] (c (WitnessField ctx))
    , HomomorphicCommit [FieldElement ctx] (c (FieldElement ctx))
    ) => SpecialSoundProtocol k i p ctx -> CommitOpen k i p c ctx
commitOpen SpecialSoundProtocol {..} =
    let
        prover' pi0 w r i =
            let m = prover pi0 w r i
            in (m, hcommit m)

        verifier' pi pms rs =
            let ms = fmap fst pms
                cs = fmap snd pms
            in (verifier pi ms rs, zipWith (-) (fmap hcommit ms) cs)
    in
        CommitOpen input prover' verifier'
