{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TypeOperators  #-}

module ZkFold.Base.Protocol.Protostar.IVC where

import           Control.DeepSeq                                  (NFData)
import           Control.Lens                                     ((^.))
import           Data.Functor.Rep                                 (Representable (..))
import           Data.Type.Equality                               (type (~))
import           Data.Zip                                         (Zip (..))
import           GHC.Generics                                     (Generic)
import           Prelude                                          (($), const)
import qualified Prelude                                          as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number                 (KnownNat, Natural, type (-))
import           ZkFold.Base.Data.Vector                          (Vector)
import           ZkFold.Base.Protocol.Protostar.Accumulator       hiding (pi)
import qualified ZkFold.Base.Protocol.Protostar.AccumulatorScheme as Acc
import           ZkFold.Base.Protocol.Protostar.AccumulatorScheme (AccumulatorScheme (..))
import           ZkFold.Base.Protocol.Protostar.AlgebraicMap      (AlgebraicMap)
import           ZkFold.Base.Protocol.Protostar.Commit            (HomomorphicCommit)
import           ZkFold.Base.Protocol.Protostar.CommitOpen
import           ZkFold.Base.Protocol.Protostar.FiatShamir
import           ZkFold.Base.Protocol.Protostar.NARK              (NARKInstanceProof (..), NARKProof (..), narkInstanceProof)
import           ZkFold.Base.Protocol.Protostar.Oracle
import           ZkFold.Base.Protocol.Protostar.SpecialSound      (SpecialSoundProtocol (input))

data IVCProof f i m c d k
    = IVCProof
    { ivcpInstance            :: i f
    , ivcpCommits             :: Vector k c
    , ivcpAccumulatorInstance :: AccumulatorInstance f i c k
    , ivcpAccumulationProof   :: Vector (d-1) c
    } deriving (GHC.Generics.Generic)

deriving instance (P.Show f, P.Show (i f), P.Show m, P.Show c) => P.Show (IVCProof f i m c d k)
deriving instance (NFData f, NFData (i f), NFData m, NFData c) => NFData (IVCProof f i m c d k)

noIVCProof :: forall f i m c d k a .
    ( Representable i
    , m ~ [f]
    , HomomorphicCommit m c
    , KnownNat (d-1)
    , KnownNat (k-1)
    , KnownNat k
    , AlgebraicMap f i d a
    ) => FiatShamir (CommitOpen a) -> i f -> IVCProof f i m c d k
noIVCProof fs pi0 = IVCProof pi0 (tabulate $ const zero) (emptyAccumulatorInstance @_ @_ @_ @_ @d fs) (tabulate $ const zero)

-- | The final result of recursion and the final accumulator.
-- Accumulation decider is an arithmetizable function which can be called on the final accumulator.
--
data IVCResult f i m c d k
    = IVCResult
    { ivcAccumulator :: Accumulator f i m c k
    , ivcProof       :: IVCProof f i m c d k
    } deriving (GHC.Generics.Generic)

deriving instance (P.Show f, P.Show (i f), P.Show m, P.Show c) => P.Show (IVCResult f i m c d k)
deriving instance (NFData f, NFData (i f), NFData m, NFData c) => NFData (IVCResult f i m c d k)

ivcInitialize :: forall f i m c (d :: Natural) k a .
    ( Representable i
    , m ~ [f]
    , HomomorphicCommit m c
    , KnownNat (d-1)
    , KnownNat (k-1)
    , KnownNat k
    , AlgebraicMap f i d a
    ) => FiatShamir (CommitOpen a) -> i f -> IVCResult f i m c d k
ivcInitialize fs pi0 = IVCResult (emptyAccumulator @_ @_ @_ @_ @d fs) (noIVCProof fs pi0)

ivcIterate :: forall f i m c (d :: Natural) k a .
    ( SpecialSoundProtocol f i m c d k a
    , Ring f
    , HomomorphicCommit m c
    , RandomOracle (i f) f
    , RandomOracle c f
    , KnownNat k
    , AccumulatorScheme f i m c d k (FiatShamir (CommitOpen a))
    ) => FiatShamir (CommitOpen a) -> IVCResult f i m c d k -> i f -> IVCResult f i m c d k
ivcIterate fs (IVCResult acc0 _) pi0 =
    let
        narkIP@(NARKInstanceProof pi (NARKProof cs _)) = narkInstanceProof @_ @_ @_ @_ @d fs pi0
        (acc, pf) = Acc.prover fs acc0 narkIP
        proof = IVCProof pi cs (acc0^.x) pf
    in
        IVCResult acc proof

ivcVerify :: forall f i m c d k a .
    ( AdditiveGroup f
    , Zip i
    , SpecialSoundProtocol f i m c d k a
    , AccumulatorScheme f i m c d k a
    ) => a -> i f -> IVCResult f i m c d k -> ((f, i f, Vector (k-1) f, Vector k c, c), (Vector k c, c), i f)
ivcVerify a pi IVCResult {..} =
    let
        IVCProof {..} = ivcProof
        acc   = ivcAccumulator
        accX  = acc^.x
        accX0 = ivcpAccumulatorInstance
        pi0   = ivcpInstance
        cs    = ivcpCommits
        pf    = ivcpAccumulationProof
    in
        ( Acc.verifier @f @i @m @c @d @k @a pi0 cs accX0 accX pf
        , decider @f @i @m @c @d @k @a a acc
        , zipWith (-) (input @f @i @m @c @d @k a pi0) pi
        )
