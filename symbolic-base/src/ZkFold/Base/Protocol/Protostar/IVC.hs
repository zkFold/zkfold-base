{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.Protostar.IVC where

import           Control.DeepSeq                                  (NFData)
import           Control.Lens                                     ((^.))
import           Data.Functor.Rep                                 (Representable(..))
import           Data.Type.Equality                               (type (~))
import           GHC.Generics                                     (Generic)
import qualified Prelude                                          as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number                 (type (-), KnownNat)
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
import           ZkFold.Base.Protocol.Protostar.SpecialSound      (SpecialSoundProtocol)

-- | The final result of recursion and the final accumulator.
-- Accumulation decider is an arithmetizable function which can be called on the final accumulator.
--
data IVCInstanceProof f i c m k d
    = IVCInstanceProof
    { ivcInstance :: i f
    , ivcCommits  :: Vector k c -- NARK proof π.x
    , ivcAcc      :: Accumulator f i c m k
    , ivcAcc'     :: Accumulator f i c m k
    , ivcAccProof :: Vector (d-1) c
    } deriving (GHC.Generics.Generic)

deriving instance (P.Show f, P.Show (i f), P.Show c, P.Show m) => P.Show (IVCInstanceProof f i c m k d)
deriving instance (NFData f, NFData (i f), NFData c, NFData m) => NFData (IVCInstanceProof f i c m k d)

ivcInitialize ::
    ( AdditiveMonoid f
    , Representable i
    , AdditiveMonoid c
    , m ~ Vector 1 f 
    ) => IVCInstanceProof f i c m 1 d
ivcInitialize =
    let acc = Accumulator (AccumulatorInstance (tabulate zero) (singleton zero) (unsafeToVector []) zero zero) (singleton zero)
    in IVCInstanceProof (tabulate zero) (singleton zero) acc acc (unsafeToVector [])

ivcIterate :: forall f i c m k d a .
    ( Ring f
    , KnownNat k
    , SpecialSoundProtocol f i m k a
    , HomomorphicCommit m c
    , RandomOracle (i f) f
    , RandomOracle c f
    , AccumulatorScheme f i c m k d (FiatShamir f (CommitOpen m c a))
    ) => FiatShamir f (CommitOpen m c a) -> IVCInstanceProof f i c m k d -> i f -> IVCInstanceProof f i c m k d
ivcIterate fs (IVCInstanceProof _ _ _ acc' _) pi' =
    let narkIP@(InstanceProofPair _ (NARKProof cs _)) = instanceProof fs pi'
        (acc'', accProof') = Acc.prover fs acc' narkIP
    in IVCInstanceProof pi' cs acc' acc'' accProof'

ivcVerify :: forall f i c m k d a .
    ( AccumulatorScheme f i c m k d a
    ) => a -> IVCInstanceProof f i c m k d -> ((f, i f, Vector (k-1) f, Vector k c, c), (Vector k c, c))
ivcVerify a (IVCInstanceProof {..}) =
    let accX  = ivcAcc^.x
        accX' = ivcAcc'^.x
    in
        ( Acc.verifier @f @i @c @m @k @d @a ivcInstance ivcCommits accX accX' ivcAccProof
        , decider @f @i @c @m @k @d @a a ivcAcc')
