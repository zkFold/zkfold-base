{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.CommitOpen where

import           GHC.Generics
import           Prelude                                     hiding (Eq (..), length, (&&), (/=), (==))

import           ZkFold.Base.Data.ByteString
import           ZkFold.Base.Protocol.Protostar.Oracle
import           ZkFold.Base.Protocol.Protostar.SpecialSound (AlgebraicMap (..), SpecialSoundProtocol (..),
                                                              SpecialSoundTranscript)
import           ZkFold.Prelude                              (length)
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.Eq

data CommitOpen m c a = CommitOpen ([m] -> c) a

instance RandomOracle a b => RandomOracle (CommitOpen m c a) b where
    oracle (CommitOpen _ a) = oracle a

data CommitOpenProverMessage m c = Commit c | Open [m]
    deriving Generic

instance (Binary c, Binary m) => Binary (CommitOpenProverMessage m c) where
      put (Commit c)  = putWord8 0 <> put c
      put (Open msgs) = putWord8 1 <> put msgs
      get = do
            flag <- getWord8
            if flag == 0 then Commit <$> get
            else if flag == 1 then Open <$> get
            else fail ("Binary (CommitOpenProverMessage t c a): unexpected flag " <> show flag)

instance
    ( SpecialSoundProtocol f a
    , BoolType (VerifierOutput f a)
    , Eq (VerifierOutput f a) [c]
    , m ~ ProverMessage f a
    ) => SpecialSoundProtocol f (CommitOpen m c a) where
      type Witness f (CommitOpen m c a)         = (Witness f a, [m])
      type Input f (CommitOpen m c a)           = Input f a
      type ProverMessage f (CommitOpen m c a)   = CommitOpenProverMessage m c
      type VerifierMessage f (CommitOpen m c a) = VerifierMessage f a
      type VerifierOutput f (CommitOpen m c a)  = VerifierOutput f a

      type Degree (CommitOpen m c a)            = Degree a

      outputLength (CommitOpen _ a) = outputLength @f a

      rounds (CommitOpen _ a) = rounds @f a + 1

      prover (CommitOpen cm a) (w, ms) i ts
            | length ts /= length ms  = error "Invalid transcript length"
            | length ts < rounds @f a = Commit $ cm [prover @f a w i $ zip ms $ map snd ts]
            | otherwise               = Open ms

      verifier (CommitOpen cm a) i ((Open ms):mss) (_:ts) = map (cm . pure) ms == map f mss && verifier @f a i ms ts
            where f (Commit c) = c
                  f _          = error "Invalid message"
      verifier _ _ _ _ = error "Invalid transcript"

instance (AlgebraicMap f a, m ~ MapMessage f a) => AlgebraicMap f (CommitOpen m c a) where
      type MapInput f (CommitOpen m c a)     = MapInput f a
      type MapMessage f (CommitOpen m c a)   = CommitOpenProverMessage m c

      algebraicMap (CommitOpen _ a) i ((Open ms):_) ts = algebraicMap @f a i ms ts
      algebraicMap _ _ _ _                             = error "CommitOpen algebraic map: invalid transcript"


commits
    :: forall f a c m
    .  SpecialSoundTranscript f (CommitOpen m c a) -> [c]
commits = map f
      where
          f :: (ProverMessage f (CommitOpen m c a), VerifierMessage f (CommitOpen m c a)) -> c
          f (Commit c, _) = c
          f _             = error "Invalid message"

opening
    :: forall f a c m
    .  SpecialSoundProtocol f a
    => BoolType (VerifierOutput f a)
    => Eq (VerifierOutput f a) [c]
    => m ~ ProverMessage f a
    => CommitOpen m c a
    -> Witness f a
    -> Input f a
    -> (SpecialSoundTranscript f (CommitOpen m c a) -> ProverMessage f (CommitOpen m c a) -> VerifierMessage f a)
    -> ([m], SpecialSoundTranscript f (CommitOpen m c a))
opening a'@(CommitOpen _ a) w i challenge =
      let f (ms, ts) _ =
                  let rs  = snd <$> ts
                      tsA = zip ms rs
                      m   = prover @f a w i tsA
                      c   = prover @f a' (w, ms) i ts
                  in (ms ++ [m], ts ++ [(c, challenge ts c)])
      in foldl f ([], []) [1 .. rounds @f a]
