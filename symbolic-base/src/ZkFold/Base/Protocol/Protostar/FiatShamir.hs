{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Protocol.Protostar.FiatShamir where

import           GHC.Generics                                (Generic)
import           Prelude                                     hiding (Bool (..), Eq (..), length, pi, unzip)

import           ZkFold.Base.Algebra.Basic.Class             (Ring)
import           ZkFold.Base.Algebra.Basic.Number            (KnownNat, value)
import           ZkFold.Base.Data.Vector                     (Vector, item, unsafeToVector)
import           ZkFold.Base.Protocol.Protostar.Commit       (HomomorphicCommit)
import           ZkFold.Base.Protocol.Protostar.CommitOpen
import           ZkFold.Base.Protocol.Protostar.Oracle       (RandomOracle (..))
import           ZkFold.Base.Protocol.Protostar.SpecialSound (SpecialSoundProtocol (..))
import           ZkFold.Prelude                              (length)

newtype FiatShamir a = FiatShamir a
    deriving Generic

instance
    ( SpecialSoundProtocol f i m c d k a
    , Ring f
    , HomomorphicCommit m c
    , RandomOracle (i f) f
    , RandomOracle c f
    , KnownNat k
    ) => SpecialSoundProtocol f i (Vector k (m, c)) c d 1 (FiatShamir (CommitOpen a)) where
        type VerifierOutput f i (Vector k (m, c)) c d 1 (FiatShamir (CommitOpen a)) = VerifierOutput f i (m, c) c d k (CommitOpen a)

        prover (FiatShamir a) pi _ _ =
            let r0 = oracle pi
                f (ms, cs, rs) _ =
                  let r   = last rs
                      (m, c) = prover @f @i @(m, c) @c @d @k a pi r (length ms)
                  in (ms ++ [m], cs ++ [c], rs ++ [oracle (r, c)])

                (ms', cs', _) = foldl f ([], [], [r0]) [1 .. value @k]
            in unsafeToVector $ zip ms' cs'

        verifier (FiatShamir a) pi pms' _ =
            let pms = item pms'
                r0 = oracle pi
                rs = unsafeToVector $ tail $ tail $ foldl (\acc pm -> acc ++ [oracle @(f, c) (last acc, snd pm)]) [r0] pms
            in verifier @f @i @(m, c) @c @d @k a pi pms rs
