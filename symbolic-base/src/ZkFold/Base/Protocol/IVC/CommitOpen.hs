module ZkFold.Base.Protocol.IVC.CommitOpen where

import           Data.Zip                              (zipWith)
import           Prelude                               hiding (Num (..), length, pi, tail, zipWith, (&&))

import           ZkFold.Base.Algebra.Basic.Class       (AdditiveGroup (..))
import           ZkFold.Base.Data.Vector               (Vector)
import           ZkFold.Base.Protocol.IVC.Commit       (HomomorphicCommit (hcommit))
import           ZkFold.Base.Protocol.IVC.SpecialSound (SpecialSoundProtocol (..))

type CommitOpen d k i p o m c f = SpecialSoundProtocol d k i p (Vector k c, o) (m, c) c f

commitOpen :: HomomorphicCommit m c => SpecialSoundProtocol d k i p o m c f -> CommitOpen d k i p o m c f
commitOpen SpecialSoundProtocol {..} =
    let
        prover' pi0 w r i =
            let m = prover pi0 w r i
            in (m, hcommit m)

        verifier' pi pms rs =
            let ms = fmap fst pms
                cs = fmap snd pms
            in (zipWith (-) (fmap hcommit ms) cs, verifier pi ms rs)
    in
        SpecialSoundProtocol input prover' verifier'
