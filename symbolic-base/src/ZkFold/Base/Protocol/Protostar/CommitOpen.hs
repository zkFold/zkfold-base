{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.Protostar.CommitOpen where

import           GHC.Generics
import           Prelude                                     hiding (Num (..), length, pi, (&&))

import           ZkFold.Base.Algebra.Basic.Class             (AdditiveGroup (..), (+))
import           ZkFold.Base.Protocol.Protostar.Commit       (HomomorphicCommit (hcommit))
import           ZkFold.Base.Protocol.Protostar.Oracle
import           ZkFold.Base.Protocol.Protostar.SpecialSound (AlgebraicMap (..), SpecialSoundProtocol (..))
import Data.Kind (Type)

newtype CommitOpen (m :: Type) (c :: Type) a = CommitOpen a

instance RandomOracle a b => RandomOracle (CommitOpen m c a) b where
    oracle (CommitOpen a) = oracle a

data CommitOpenProverMessage m c = Commit c | Open [m]
    deriving Generic

instance
    ( SpecialSoundProtocol f a
    , ProverMessage f a ~ m
    , HomomorphicCommit m c
    ) => SpecialSoundProtocol f (CommitOpen m c a) where
      type Witness f (CommitOpen m c a)         = (Witness f a, [m])
      type Input f (CommitOpen m c a)           = Input f a
      type ProverMessage f (CommitOpen m c a)   = CommitOpenProverMessage m c
      type VerifierMessage f (CommitOpen m c a) = VerifierMessage f a
      type VerifierOutput f (CommitOpen m c a)  = ([c], VerifierOutput f a)

      type Degree (CommitOpen m c a)            = Degree a

      outputLength (CommitOpen a) = outputLength @f a

      rounds (CommitOpen a) = rounds @f a + 1

      prover (CommitOpen a) (w, ms) pi r i
            | i <= rounds @f a = Commit $ hcommit $ prover @f a w pi r i
            | otherwise        = Open ms

      verifier (CommitOpen a) pi ((Open ms):mss) (_:rs) = (zipWith (-) (map hcommit ms) (map f mss), verifier @f a pi ms rs)
            where f (Commit c) = c
                  f _          = error "Invalid message"
      verifier _ _ _ _ = error "Invalid transcript"

instance (AlgebraicMap f a, m ~ MapMessage f a) => AlgebraicMap f (CommitOpen m c a) where
      type MapInput f (CommitOpen m c a)     = MapInput f a
      type MapMessage f (CommitOpen m c a)   = CommitOpenProverMessage m c

      algebraicMap (CommitOpen a) i ((Open ms):_) rs = algebraicMap @f a i ms rs
      algebraicMap _ _ _ _                           = error "CommitOpen algebraic map: invalid transcript"
