module ZkFold.Base.Protocol.Protostar.FiatShamir where

import           GHC.Generics                                (Generic)
import           Prelude                                     hiding (Bool (..), Eq (..), length, unzip, pi)

import           ZkFold.Base.Algebra.Basic.Number            (value)
import           ZkFold.Base.Data.Vector                     (Vector, unsafeToVector, item)
import           ZkFold.Base.Protocol.Protostar.Commit       (HomomorphicCommit)
import           ZkFold.Base.Protocol.Protostar.CommitOpen
import           ZkFold.Base.Protocol.Protostar.Oracle       (RandomOracle (..))
import           ZkFold.Base.Protocol.Protostar.SpecialSound (BasicSpecialSoundProtocol, SpecialSoundProtocol (..))
import           ZkFold.Prelude                              (length)

newtype FiatShamir f a = FiatShamir a
    deriving Generic

instance
    ( BasicSpecialSoundProtocol f pi m k a
    , RandomOracle pi f
    , RandomOracle (f, c) f
    , HomomorphicCommit m c
    ) => SpecialSoundProtocol f pi (Vector k (m, c)) 1 (FiatShamir f (CommitOpen m c a)) where
        type VerifierOutput f pi (Vector k (m, c)) 1 (FiatShamir f (CommitOpen m c a))  = VerifierOutput f pi (m, c) k (CommitOpen m c a)

        outputLength (FiatShamir a) = outputLength @f @pi @(m, c) @k a

        prover (FiatShamir a) pi _ _ =
            let r0 = oracle pi
                f (ms, cs, rs) _ =
                  let r   = last rs
                      (m, c) = prover @f @pi @(m, c) @k a pi r (length ms)
                  in (ms ++ [m], cs ++ [c], rs ++ [oracle @(f, c) (r, c)])

                (ms', cs', _) = foldl f ([], [], [r0]) [1 .. value @k]
            in unsafeToVector $ zip ms' cs'

        verifier (FiatShamir a) pi pms' _ =
            let pms = item pms'
                r0 = oracle pi
                rs = unsafeToVector $ tail $ tail $ foldl (\acc pm -> acc ++ [oracle @(f, c) (last acc, snd pm)]) [r0] pms
            in verifier @f @pi @(m, c) @k a pi pms rs
