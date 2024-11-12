{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.FiatShamir where

import           GHC.Generics
import           Prelude                                     hiding (Bool (..), Eq (..), length, pi)

import           ZkFold.Base.Protocol.Protostar.Commit       (HomomorphicCommit)
import           ZkFold.Base.Protocol.Protostar.CommitOpen
import           ZkFold.Base.Protocol.Protostar.Oracle       (RandomOracle (..))
import           ZkFold.Base.Protocol.Protostar.SpecialSound (BasicSpecialSoundProtocol, SpecialSoundProtocol (..))
import           ZkFold.Prelude                              (length)

newtype FiatShamir f a = FiatShamir a
    deriving Generic

instance
    ( BasicSpecialSoundProtocol f pi m a
    , RandomOracle pi f
    , RandomOracle (f, c) f
    , HomomorphicCommit m c
    ) => SpecialSoundProtocol f pi [(c, m)] (FiatShamir f (CommitOpen m c a)) where
        type Witness f (FiatShamir f (CommitOpen m c a))         = Witness f a
        type VerifierMessage f (FiatShamir f (CommitOpen m c a)) = ()
        type VerifierOutput f (FiatShamir f (CommitOpen m c a))  = VerifierOutput f (CommitOpen m c a)

        outputLength (FiatShamir a) = outputLength @f @pi @(CommitOpenProverMessage m c) a

        rounds _ = 1

        prover (FiatShamir a'@(CommitOpen a)) w pi _ _ =
            let r0 = oracle pi
                f (ms, cs, rs) _ =
                  let r   = last rs
                      m   = prover @f @pi @m a w pi r (length ms)
                      c   = case prover @f @pi @(CommitOpenProverMessage m c) a' (w, ms) pi r (length ms) of
                                Commit c' -> c'
                                _         -> error "Invalid message"
                  in (ms ++ [m], cs ++ [c], rs ++ [oracle @(f, c) (r, c)])

                (ms', cs', _) = foldl f ([], [], [r0]) [1 .. rounds @f @pi @m a]
            in zip cs' ms'

        verifier (FiatShamir a) pi [ms'] _ =
            let (cs, ms) = unzip ms'
                r0 = oracle pi
                rs = foldl (\acc c -> acc ++ [oracle @(f, c) (last acc, c)]) [r0] cs
            in verifier @f @pi a pi (Open ms : map Commit cs) rs
        verifier _ _ _ _ = error "Invalid message"
