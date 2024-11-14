{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Base.Protocol.Protostar.CommitOpen where

import           Data.Kind                                   (Type)
import           Data.Zip                                    (zipWith)
import           Prelude                                     hiding (Num (..), length, pi, zipWith, tail, (&&))

import           ZkFold.Base.Algebra.Basic.Class             (AdditiveGroup (..))
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Base.Protocol.Protostar.Commit       (HomomorphicCommit (hcommit))
import           ZkFold.Base.Protocol.Protostar.Oracle
import           ZkFold.Base.Protocol.Protostar.SpecialSound (SpecialSoundProtocol (..))

newtype CommitOpen (m :: Type) (c :: Type) a = CommitOpen a

instance RandomOracle a b => RandomOracle (CommitOpen m c a) b where
    oracle (CommitOpen a) = oracle a

instance
    ( SpecialSoundProtocol f i m k a
    , HomomorphicCommit m c
    ) => SpecialSoundProtocol f i (m, c) k (CommitOpen m c a) where
      type VerifierOutput f i (m, c) k (CommitOpen m c a)  = (Vector k c, VerifierOutput f i m k a)

      outputLength (CommitOpen a) = outputLength @f @i @m @k a

      prover (CommitOpen a) pi r i =
            let m = prover @f @i @m @k a pi r i
            in (m, hcommit m)

      verifier (CommitOpen a) pi pms rs =
            let ms = fmap fst pms
                cs = fmap snd pms
            in (zipWith (-) (fmap hcommit ms) cs, verifier @f @i @m a pi ms rs)
