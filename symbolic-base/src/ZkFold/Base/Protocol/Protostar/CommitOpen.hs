{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Base.Protocol.Protostar.CommitOpen where

import           Data.Kind                                   (Type)
import           GHC.Generics
import           Prelude                                     hiding (Num (..), length, pi, (&&))

import           ZkFold.Base.Algebra.Basic.Class             (AdditiveGroup (..), (+))
import           ZkFold.Base.Protocol.Protostar.Commit       (HomomorphicCommit (hcommit))
import           ZkFold.Base.Protocol.Protostar.Oracle
import           ZkFold.Base.Protocol.Protostar.SpecialSound (BasicSpecialSoundProtocol, SpecialSoundProtocol (..))

newtype CommitOpen (m :: Type) (c :: Type) a = CommitOpen a

instance RandomOracle a b => RandomOracle (CommitOpen m c a) b where
    oracle (CommitOpen a) = oracle a

data CommitOpenProverMessage m c = Commit c | Open [m]
    deriving Generic

instance
    ( BasicSpecialSoundProtocol f pi m a
    , HomomorphicCommit m c
    ) => SpecialSoundProtocol f pi m (CommitOpen m c a) where
      type Witness f (CommitOpen m c a)         = (Witness f a, [m])
      type ProverMessage f (CommitOpen m c a)   = CommitOpenProverMessage m c
      type VerifierMessage f (CommitOpen m c a) = VerifierMessage f a
      type VerifierOutput f (CommitOpen m c a)  = ([c], VerifierOutput f a)

      outputLength (CommitOpen a) = outputLength @f @pi @m a

      rounds (CommitOpen a) = rounds @f @pi @m a + 1

      prover (CommitOpen a) (w, ms) pi r i
            | i <= rounds @f @pi @m a = Commit $ hcommit $ prover @f @pi @m a w pi r i
            | otherwise        = Open ms

      verifier (CommitOpen a) pi ((Open ms):mss) (_:rs) = (zipWith (-) (map hcommit ms) (map f mss), verifier @f @pi @m a pi ms rs)
            where f (Commit c) = c
                  f _          = error "Invalid message"
      verifier _ _ _ _ = error "Invalid transcript"
