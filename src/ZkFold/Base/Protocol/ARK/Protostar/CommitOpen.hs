{-# LANGUAGE TypeApplications    #-}

module ZkFold.Base.Protocol.ARK.Protostar.CommitOpen where

import           Prelude                                         hiding (length)

import           ZkFold.Base.Data.ByteString                     (ToByteString(..))
import           ZkFold.Base.Protocol.ARK.Protostar.SpecialSound (SpecialSoundProtocol(..), SpecialSoundTranscript)
import           ZkFold.Prelude                                  (length)

data CommitOpen c a = CommitOpen (ProverMessage a -> c) a

data CommitOpenProverMessage c a = Commit c | Open [ProverMessage a]
instance ToByteString c => ToByteString (CommitOpenProverMessage c a) where
      toByteString (Commit c) = toByteString c
      toByteString _          = mempty

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

      verifier (CommitOpen cm a) i ((Open ms, _) : ts) = map cm ms == map f ts && verifier a i (zip ms $ map snd ts)
            where f (Commit c, _) = c
                  f _             = error "Invalid message"
      verifier _ _ _ = error "Invalid transcript"

commits :: SpecialSoundTranscript (CommitOpen c a) -> [c]
commits = map f
      where f (Commit c, _) = c
            f _             = error "Invalid message"

opening :: forall a c . (SpecialSoundProtocol a, Eq c)
        => CommitOpen c a
        -> Witness a
        -> Input a
        -> (SpecialSoundTranscript (CommitOpen c a) -> ProverMessage (CommitOpen c a) -> VerifierMessage a)
        -> ([ProverMessage a], SpecialSoundTranscript (CommitOpen c a))
opening a'@(CommitOpen _ a) w i challenge =
      let f (ms, ts) _ =
                  let rs  = snd <$> ts
                      tsA = zip ms rs
                      m   = prover a w i tsA
                      c   = prover a' (w, ms) i ts
                  in (ms ++ [m], ts ++ [(c, challenge ts c)])
      in foldl f ([], []) [1 .. rounds @a]