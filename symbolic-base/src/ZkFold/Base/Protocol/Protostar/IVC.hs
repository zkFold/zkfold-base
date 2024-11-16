{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveAnyClass      #-}

module ZkFold.Base.Protocol.Protostar.IVC where

import           Control.DeepSeq                                  (NFData)
import           Control.Lens                                     ((^.))
import           GHC.Generics                                     (Generic)
import qualified Prelude                                          as P

import           ZkFold.Base.Algebra.Basic.Class
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
data IVCInstanceProof pi f c m
    = IVCInstanceProof
    { ivcInstance :: pi
    , ivcCommits  :: [c] -- NARK proof π.x
    , ivcAcc      :: Accumulator pi f c m
    , ivcAcc'     :: Accumulator pi f c m
    , ivcAccProof :: [c]
    } deriving (GHC.Generics.Generic)

deriving instance (P.Show pi, P.Show f, P.Show c, P.Show m) => P.Show (IVCInstanceProof pi f c m)
deriving instance (NFData pi, NFData f, NFData c, NFData m) => NFData (IVCInstanceProof pi f c m)

ivcInitialize ::
    ( AdditiveMonoid f
    , AdditiveMonoid pi
    , AdditiveMonoid c
    ) => IVCInstanceProof pi f c m
ivcInitialize =
    let acc = Accumulator (AccumulatorInstance zero [zero] [] zero zero) []
    -- TODO: we need the proper number of commits and accumulation proof elements
    in IVCInstanceProof zero [zero] acc acc []

ivcIterate :: forall f pi c m a .
    ( BasicSpecialSoundProtocol f pi m a
    , Ring f
    , RandomOracle f f
    , RandomOracle pi f
    , RandomOracle c f
    , HomomorphicCommit m c
    , AccumulatorScheme pi f c m (FiatShamir f (CommitOpen m c a))
    ) => FiatShamir f (CommitOpen m c a) -> IVCInstanceProof pi f c m -> pi -> IVCInstanceProof pi f c m
ivcIterate fs (IVCInstanceProof _ _ _ acc' _) pi' =
    let narkIP@(InstanceProofPair _ (NARKProof cs _)) = instanceProof fs pi'
        (acc'', accProof') = Acc.prover fs acc' narkIP
    in IVCInstanceProof pi' cs acc' acc'' accProof'

ivcVerify :: forall pi f c m a .
    ( AccumulatorScheme pi f c m a
    ) => a -> IVCInstanceProof pi f c m -> ((f, pi, [f], [c], c), ([c], c))
ivcVerify a (IVCInstanceProof {..}) =
    let accX  = ivcAcc^.x
        accX' = ivcAcc'^.x
    in
        ( Acc.verifier @pi @f @c @m @a ivcInstance ivcCommits accX accX' ivcAccProof
        , decider @pi @f @c @m @a a ivcAcc')

ivcVerify':: forall pi f c m a .
    ( AccumulatorScheme pi f c m a
    ) => a -> IVCInstanceProof pi f c m -> ((f, pi, f, c, c), (c, c))
ivcVerify' a ip =
    let ((x1, x2, x3, x4, x5), (x6, x7)) = ivcVerify @pi @f @c @m @a a ip
    in ((x1, x2, P.head x3, P.head x4, x5), (P.head x6, x7))
