{-# LANGUAGE TypeApplications    #-}

module ZkFold.Base.Protocol.ARK.Protostar.CommitOpen where

import           Prelude                                         hiding (length)

import           ZkFold.Base.Data.ByteString                     (ToByteString(..))
import           ZkFold.Base.Protocol.ARK.Protostar.SpecialSound (SpecialSoundProtocol(..), SpecialSoundTranscript)
import           ZkFold.Prelude                                  (length)

data CommitOpen f c a = CommitOpen (ProverMessage f a -> c) a

data CommitOpenProverMessage t c a = Commit c | Open [ProverMessage t a]
instance ToByteString c => ToByteString (CommitOpenProverMessage t c a) where
      toByteString (Commit c) = toByteString c
      toByteString _          = mempty

instance (SpecialSoundProtocol f a, Eq c) => SpecialSoundProtocol f (CommitOpen f c a) where
      type Witness f (CommitOpen f c a)         = (Witness f a, [ProverMessage f a])
      type Input f (CommitOpen f c a)           = Input f a
      type ProverMessage t (CommitOpen f c a)   = CommitOpenProverMessage t c a
      type VerifierMessage t (CommitOpen f c a) = VerifierMessage t a

      type Dimension (CommitOpen f c a)         = Dimension a
      type Degree (CommitOpen f c a)            = Degree a

      rounds a = rounds @f a + 1

      prover (CommitOpen cm a) (w, ms) i ts
            | length ts /= length ms  = error "Invalid transcript length"
            | length ts < rounds @f a = Commit $ cm $ prover @f a w i $ zip ms $ map snd ts
            | otherwise               = Open ms

      -- TODO: Implement this
      verifier' = undefined

      verifier (CommitOpen cm a) i ((Open ms, _) : ts) = map cm ms == map f ts && verifier @f a i (zip ms $ map snd ts)
            where f (Commit c, _) = c
                  f _             = error "Invalid message"
      verifier _ _ _ = error "Invalid transcript"

commits :: SpecialSoundTranscript t (CommitOpen f c a) -> [c]
commits = map f
      where f (Commit c, _) = c
            f _             = error "Invalid message"

opening :: forall f a c . (SpecialSoundProtocol f a, Eq c)
        => CommitOpen f c a
        -> Witness f a
        -> Input f a
        -> (SpecialSoundTranscript f (CommitOpen f c a) -> ProverMessage f (CommitOpen f c a) -> VerifierMessage f a)
        -> ([ProverMessage f a], SpecialSoundTranscript f (CommitOpen f c a))
opening a'@(CommitOpen _ a) w i challenge =
      let f (ms, ts) _ =
                  let rs  = snd <$> ts
                      tsA = zip ms rs
                      m   = prover @f a w i tsA
                      c   = prover a' (w, ms) i ts
                  in (ms ++ [m], ts ++ [(c, challenge ts c)])
      in foldl f ([], []) [1 .. rounds @f a]
