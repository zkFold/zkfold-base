{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.CommitOpen where

import           GHC.Generics
import           Prelude                                         hiding (length)

import           ZkFold.Base.Data.ByteString
import           ZkFold.Base.Protocol.Protostar.SpecialSound (SpecialSoundProtocol (..), SpecialSoundTranscript)
import           ZkFold.Base.Protocol.Protostar.Oracle
import           ZkFold.Prelude                                  (length)

data CommitOpen f c a = CommitOpen ([ProverMessage f a] -> c) a

instance RandomOracle a b => RandomOracle (CommitOpen f c a) b where
    oracle (CommitOpen _ a) = oracle a

data CommitOpenProverMessage t c a = Commit c | Open [ProverMessage t a]
    deriving Generic

instance (Binary c, Binary (ProverMessage t a)) => Binary (CommitOpenProverMessage t c a) where
      put (Commit c)  = putWord8 0 <> put c
      put (Open msgs) = putWord8 1 <> put msgs
      get = do
            flag <- getWord8
            if flag == 0 then Commit <$> get
            else if flag == 1 then Open <$> get
            else fail ("Binary (CommitOpenProverMessage t c a): unexpected flag " <> show flag)

instance (SpecialSoundProtocol f a, Eq c) => SpecialSoundProtocol f (CommitOpen f c a) where
      type Witness f (CommitOpen f c a)         = (Witness f a, [ProverMessage f a])
      type Input f (CommitOpen f c a)           = Input f a
      type ProverMessage t (CommitOpen f c a)   = CommitOpenProverMessage t c a
      type VerifierMessage t (CommitOpen f c a) = VerifierMessage t a

      type Degree (CommitOpen f c a)            = Degree a

      outputLength (CommitOpen _ a) = outputLength @f a

      rounds a = rounds @f a + 1

      prover (CommitOpen cm a) (w, ms) i ts
            | length ts /= length ms  = error "Invalid transcript length"
            | length ts < rounds @f a = Commit $ cm [prover @f a w i $ zip ms $ map snd ts]
            | otherwise               = Open ms

      -- TODO: Implement this

      algebraicMap = undefined

      verifier (CommitOpen cm a) i ((Open ms):mss) (_:ts) = map (cm . pure) ms == map f mss && verifier @f a i ms ts
            where f (Commit c) = c
                  f _          = error "Invalid message"
      verifier _ _ _ _ = error "Invalid transcript"

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
