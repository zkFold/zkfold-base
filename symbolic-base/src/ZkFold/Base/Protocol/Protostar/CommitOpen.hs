{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.CommitOpen where

import           Data.Zip                                    (zipWith)
import           Prelude                                     hiding (Num (..), length, pi, tail, zipWith, (&&))

import           ZkFold.Base.Algebra.Basic.Class             (AdditiveGroup (..))
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Base.Protocol.Protostar.Commit       (HomomorphicCommit (hcommit))
import           ZkFold.Base.Protocol.Protostar.Oracle
import           ZkFold.Base.Protocol.Protostar.SpecialSound (SpecialSoundProtocol (..))

newtype CommitOpen a = CommitOpen a

instance RandomOracle a b => RandomOracle (CommitOpen a) b where
    oracle (CommitOpen a) = oracle a

instance
    ( SpecialSoundProtocol f i m c d k a
    , HomomorphicCommit m c
    ) => SpecialSoundProtocol f i (m, c) c d k (CommitOpen a) where
      type VerifierOutput f i (m, c) c d k (CommitOpen a) = (Vector k c, VerifierOutput f i m c d k a)

      input (CommitOpen a) = input @_ @_ @m @c @d @k a

      prover (CommitOpen a) pi r i =
            let m = prover @f @i @m @c @d @k a pi r i
            in (m, hcommit m)

      verifier (CommitOpen a) pi pms rs =
            let ms = fmap fst pms
                cs = fmap snd pms
            in (zipWith (-) (fmap hcommit ms) cs, verifier @f @i @m @c @d @k a pi ms rs)
