{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.IVC.CommitOpen where

import           Data.Zip                              (zipWith)
import           Prelude                               hiding (Num (..), length, pi, tail, zipWith, (&&))

import           ZkFold.Base.Algebra.Basic.Class       (AdditiveGroup (..))
import           ZkFold.Base.Data.Vector               (Vector)
import           ZkFold.Base.Protocol.IVC.Commit       (HomomorphicCommit (hcommit))
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Base.Protocol.IVC.SpecialSound (SpecialSoundProtocol (..))

newtype CommitOpen a = CommitOpen a

instance RandomOracle algo a b => RandomOracle algo (CommitOpen a) b where
    oracle (CommitOpen a) = oracle @algo a

instance
    ( SpecialSoundProtocol f i p m c d k a
    , HomomorphicCommit m c
    ) => SpecialSoundProtocol f i p (m, c) c d k (CommitOpen a) where
      type VerifierOutput f i p (m, c) c d k (CommitOpen a) = (Vector k c, VerifierOutput f i p m c d k a)

      input (CommitOpen a) = input @_ @_ @_ @m @c @d @k a

      prover (CommitOpen a) pi0 w r i =
            let m = prover @f @i @_ @m @c @d @k a pi0 w r i
            in (m, hcommit m)

      verifier (CommitOpen a) pi pms rs =
            let ms = fmap fst pms
                cs = fmap snd pms
            in (zipWith (-) (fmap hcommit ms) cs, verifier @f @_ @p @m @c @d @k a pi ms rs)
