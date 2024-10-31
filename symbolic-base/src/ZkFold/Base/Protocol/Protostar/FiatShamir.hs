{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.FiatShamir where

import           GHC.Generics
import           Prelude                                     hiding (Bool (..), Eq (..), length)

import           ZkFold.Base.Algebra.Basic.Class             (AdditiveGroup)
import           ZkFold.Base.Protocol.Protostar.CommitOpen
import           ZkFold.Base.Protocol.Protostar.Oracle       (RandomOracle(..))
import qualified ZkFold.Base.Protocol.Protostar.SpecialSound as SpS
import           ZkFold.Base.Protocol.Protostar.SpecialSound (SpecialSoundProtocol (..))

newtype FiatShamir f a = FiatShamir a
    deriving Generic

-- fsChallenge
--     :: forall f m c a
--     .  Binary (SpS.Input f a)
--     => Binary (VerifierMessage f a)
--     => Binary c
--     => Binary (ProverMessage f a)
--     => m ~ ProverMessage f a
--     => FiatShamir f (CommitOpen m c a)
--     -> SpecialSoundTranscript f (CommitOpen m c a)
--     -> ProverMessage f (CommitOpen m c a)
--     -> VerifierMessage f a
-- fsChallenge (FiatShamir _ ip) []           c =
--       let r0 = challenge @ByteString $ toTranscript ip :: VerifierMessage f a
--       in challenge @ByteString $ toTranscript r0 <> toTranscript c
-- fsChallenge _                 ((_, r) : _) c = challenge @ByteString $ toTranscript r <> toTranscript c

instance
    ( ProverMessage f a ~ m
    , AdditiveGroup c
    , RandomOracle (SpS.Input f a) f
    , RandomOracle (f, c) f
    , SpS.SpecialSoundProtocol f a
    ) => SpecialSoundProtocol f (FiatShamir f (CommitOpen m c a)) where
        type Witness f (FiatShamir f (CommitOpen m c a))         = SpS.Witness f a
        type Input f (FiatShamir f (CommitOpen m c a))           = SpS.Input f a
        type ProverMessage f (FiatShamir f (CommitOpen m c a))   = [(c, ProverMessage f a)]
        type VerifierMessage f (FiatShamir f (CommitOpen m c a)) = ()
        type VerifierOutput f (FiatShamir f (CommitOpen m c a))  = VerifierOutput f (CommitOpen m c a)

        type Degree (FiatShamir f (CommitOpen m c a))            = Degree (CommitOpen m c a)

        outputLength (FiatShamir a) = outputLength @f a

        rounds _ = 1

        prover (FiatShamir a'@(CommitOpen _ a)) w i _ =
            let r0 = oracle i
                f (ms, cs, rs) _ =
                  let r   = last rs
                      m   = prover @f a w i r
                      c   = case prover @f a' (w, ms) i r of
                                Commit c' -> c'
                                _         -> error "Invalid message"
                  in (ms ++ [m], cs ++ [c], rs ++ [oracle @(f, c) (r, c)])

                (ms', cs', _) = foldl f ([], [], [r0]) [1 .. rounds @f a]
            in zip cs' ms'

        verifier (FiatShamir a) i [ms'] _ =
            let (cs, ms) = unzip ms'
                r0 = oracle i
                rs = foldl (\acc c -> acc ++ [oracle @(f, c) (last acc, c)]) [r0] cs
            in verifier @f a i (Open ms : map Commit cs) rs
        verifier _ _ _ _ = error "Invalid message"

-- instance
--     ( SpS.SpecialSoundProtocol f a
--     , Binary (SpS.Input f a)
--     , Binary (VerifierMessage f a)
--     , VerifierMessage f a ~ f
--     , ProverMessage f a ~ m
--     , Binary c
--     , Binary (ProverMessage f a)
--     , BoolType (VerifierOutput f a)
--     , Eq (VerifierOutput f a) [c]
--     , VerifierOutput f a ~ P.Bool
--     ) => NonInteractiveProof (FiatShamir f (CommitOpen m c a)) core where
--       type Transcript (FiatShamir f (CommitOpen m c a))  = ByteString
--       type SetupProve (FiatShamir f (CommitOpen m c a))  = FiatShamir f (CommitOpen m c a)
--       type SetupVerify (FiatShamir f (CommitOpen m c a)) = FiatShamir f (CommitOpen m c a)
--       type Witness (FiatShamir f (CommitOpen m c a))     = SpS.Witness f a
--       type Input (FiatShamir f (CommitOpen m c a))       = (SpS.Input f a, [c])
--       type Proof (FiatShamir f (CommitOpen m c a))       = [ProverMessage f a]

--       setupProve x = x

--       setupVerify x = x

--       prove fs@(FiatShamir a ip) w =
--             let (ms, ts) = opening @f @m @c @a a w ip (fsChallenge fs)
--             in ((ip, commits @f @m @c @a ts), ms)

--       verify fs@(FiatShamir a _) (ip, cs) ms =
--             let ts' = foldl (\acc c -> acc ++ [(c, fsChallenge fs acc c)]) [] $ map Commit cs
--                 ts  = ts' ++ [(Open ms, fsChallenge fs ts' $ Open ms)]
--                 (ri, ci) = unzip ts
--             in verifier a ip ri ci

