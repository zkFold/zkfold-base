{-# LANGUAGE TypeApplications    #-}

module ZkFold.Base.Protocol.ARK.Protostar.CommitOpen where

import           Prelude        hiding (length)

import           ZkFold.Base.Protocol.ARK.Protostar.SpecialSound
import           ZkFold.Prelude (length)

data CommitOpen c a = CommitOpen (ProverMessage a -> c) a

data CommitOpenProverMessage c a = Commit c | Open [ProverMessage a]

instance (SpecialSoundProtocol a, Eq c) => SpecialSoundProtocol (CommitOpen c a) where
      type Witness (CommitOpen c a)         = (Witness a, [ProverMessage a])
      type Input (CommitOpen c a)           = Input a
      type ProverMessage (CommitOpen c a)   = CommitOpenProverMessage c a
      type VerifierMessage (CommitOpen c a) = VerifierMessage a

      rounds = rounds @a + 1

      prover (CommitOpen cm a) (w, ms) i ts
            | length ts /= length ms = error "Invalid transcript length"
            | length ts < rounds @a  = Commit $ cm $ prover @a a w i $ zip ms $ map snd ts
            | otherwise              = Open ms

      verifier (CommitOpen cm _) _ ((Open ms, _) : ts) = map cm ms == map f ts
            where f (Commit c, _) = c
                  f _             = error "Invalid message"
      verifier _ _ _ = error "Invalid transcript"