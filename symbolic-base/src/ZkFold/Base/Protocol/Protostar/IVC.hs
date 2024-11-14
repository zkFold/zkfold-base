{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.Protostar.IVC where

import           Control.DeepSeq                                  (NFData)
import           Control.Lens                                     ((^.))
import           Data.Type.Equality                               (type (~))
import           GHC.Generics                                     (Generic)
import qualified Prelude                                          as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number                 (type (-))
import           ZkFold.Base.Data.Vector                          (Vector, singleton, unsafeToVector)
import           ZkFold.Base.Protocol.Protostar.Accumulator       hiding (pi)
import qualified ZkFold.Base.Protocol.Protostar.AccumulatorScheme as Acc
import           ZkFold.Base.Protocol.Protostar.AccumulatorScheme (AccumulatorScheme (..))
import           ZkFold.Base.Protocol.Protostar.Commit            (HomomorphicCommit)
import           ZkFold.Base.Protocol.Protostar.CommitOpen
import           ZkFold.Base.Protocol.Protostar.FiatShamir
import           ZkFold.Base.Protocol.Protostar.NARK              (InstanceProofPair (..), NARKProof (..),
                                                                   instanceProof)
import           ZkFold.Base.Protocol.Protostar.Oracle
import           ZkFold.Base.Protocol.Protostar.SpecialSound      (BasicSpecialSoundProtocol)

-- | The final result of recursion and the final accumulator.
-- Accumulation decider is an arithmetizable function which can be called on the final accumulator.
--
data IVCInstanceProof pi f c m k d
    = IVCInstanceProof
    { ivcInstance :: pi
    , ivcCommits  :: Vector k c -- NARK proof π.x
    , ivcAcc      :: Accumulator pi f c m k
    , ivcAcc'     :: Accumulator pi f c m k
    , ivcAccProof :: Vector (d-1) c
    } deriving (GHC.Generics.Generic)

deriving instance (P.Show pi, P.Show f, P.Show c, P.Show m) => P.Show (IVCInstanceProof pi f c m k d)
deriving instance (NFData pi, NFData f, NFData c, NFData m) => NFData (IVCInstanceProof pi f c m k d)

ivcInitialize ::
    ( AdditiveMonoid f
    , AdditiveMonoid pi
    , AdditiveMonoid c
    , m ~ Vector 1 f
    ) => IVCInstanceProof pi f c m 1 d
ivcInitialize =
    let acc = Accumulator (AccumulatorInstance zero (singleton zero) (unsafeToVector []) zero zero) (singleton zero)
    in IVCInstanceProof zero (singleton zero) acc acc (unsafeToVector [])

ivcIterate :: forall f pi c m k d a .
    ( BasicSpecialSoundProtocol f pi m k a
    , Ring f
    , RandomOracle f f
    , RandomOracle pi f
    , RandomOracle c f
    , HomomorphicCommit m c
    , AccumulatorScheme pi f c m k d (FiatShamir f (CommitOpen m c a))
    ) => FiatShamir f (CommitOpen m c a) -> IVCInstanceProof pi f c m k d -> pi -> IVCInstanceProof pi f c m k d
ivcIterate fs (IVCInstanceProof _ _ _ acc' _) pi' =
    let narkIP@(InstanceProofPair _ (NARKProof cs _)) = instanceProof fs pi'
        (acc'', accProof') = Acc.prover fs acc' narkIP
    in IVCInstanceProof pi' cs acc' acc'' accProof'

ivcVerify :: forall pi f c m k d a .
    ( AccumulatorScheme pi f c m k d a
    ) => a -> IVCInstanceProof pi f c m k d -> ((f, pi, Vector (k-1) f, Vector k c, c), (Vector k c, c))
ivcVerify a (IVCInstanceProof {..}) =
    let accX  = ivcAcc^.x
        accX' = ivcAcc'^.x
    in
        ( Acc.verifier @pi @f @c @m @k @d @a ivcInstance ivcCommits accX accX' ivcAccProof
        , decider @pi @f @c @m @k @d @a a ivcAcc')
