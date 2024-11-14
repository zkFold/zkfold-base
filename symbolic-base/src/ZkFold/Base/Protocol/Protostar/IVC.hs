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
import           ZkFold.Base.Algebra.Basic.Number                 (type (-), KnownNat, Natural)
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
data IVCInstanceProof f i m c d k
    = IVCInstanceProof
    { ivcInstance :: i f
    , ivcCommits  :: Vector k c -- NARK proof π.x
    , ivcAcc      :: Accumulator f i m c k
    , ivcAcc'     :: Accumulator f i m c k
    , ivcAccProof :: Vector (d-1) c
    } deriving (GHC.Generics.Generic)

deriving instance (P.Show f, P.Show (i f), P.Show m, P.Show c) => P.Show (IVCInstanceProof f i m c d k)
deriving instance (NFData f, NFData (i f), NFData m, NFData c) => NFData (IVCInstanceProof f i m c d k)

ivcInitialize ::
    ( AdditiveMonoid f
    , Representable i
    , m ~ Vector 1 f
    , AdditiveMonoid c
    ) => IVCInstanceProof f i m c d 1
ivcInitialize =
    let acc = Accumulator (AccumulatorInstance (tabulate zero) (singleton zero) (unsafeToVector []) zero zero) (singleton zero)
    in IVCInstanceProof (tabulate zero) (singleton zero) acc acc (unsafeToVector [])

ivcIterate :: forall f i m c (d :: Natural) k a .
    ( SpecialSoundProtocol f i m c d k a
    , Ring f
    , HomomorphicCommit m c
    , RandomOracle (i f) f
    , RandomOracle c f
    , KnownNat k
    , AccumulatorScheme f i m c d k (FiatShamir (CommitOpen a))
    ) => FiatShamir (CommitOpen a) -> IVCInstanceProof f i m c d k -> i f -> IVCInstanceProof f i m c d k
ivcIterate fs (IVCInstanceProof _ _ _ acc' _) pi' =
    let narkIP@(InstanceProofPair _ (NARKProof cs _)) = instanceProof @_ @_ @_ @_ @d fs pi'
        (acc'', accProof') = Acc.prover fs acc' narkIP
    in IVCInstanceProof pi' cs acc' acc'' accProof'

ivcVerify :: forall f i m c d k a .
    ( AccumulatorScheme f i m c d k a
    ) => a -> IVCInstanceProof f i m c d k -> ((f, i f, Vector (k-1) f, Vector k c, c), (Vector k c, c))
ivcVerify a (IVCInstanceProof {..}) =
    let accX  = ivcAcc^.x
        accX' = ivcAcc'^.x
    in
        ( Acc.verifier @f @i @m @c @d @k @a ivcInstance ivcCommits accX accX' ivcAccProof
        , decider @f @i @m @c @d @k @a a ivcAcc')
