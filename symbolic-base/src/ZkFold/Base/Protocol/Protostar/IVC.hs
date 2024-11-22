{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TypeOperators  #-}

module ZkFold.Base.Protocol.Protostar.IVC where

import           Control.DeepSeq                                  (NFData)
import           Control.Lens                                     ((^.))
import           Data.Functor.Rep                                 (Representable (..))
import           Data.Type.Equality                               (type (~))
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
import           ZkFold.Base.Protocol.Protostar.SpecialSound      (SpecialSoundProtocol (..))

data IVCProof f i m c d k
    = IVCProof
    { ivcpAccumulatorInstance :: AccumulatorInstance f i c k
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
    ) => FiatShamir (CommitOpen a) -> IVCProof f i m c d k
noIVCProof fs = IVCProof (emptyAccumulatorInstance @_ @_ @_ @_ @d fs) (tabulate $ const zero)

-- | The final result of recursion and the final accumulator.
-- Accumulation decider is an arithmetizable function which can be called on the final accumulator.
--
data IVCResult f i m c d k
    = IVCResult
    { ivcInstance    :: i f
    , ivcCommits     :: Vector k c
    , ivcAccumulator :: Accumulator f i m c k
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
ivcInitialize fs pi0 = IVCResult pi0 (tabulate $ const zero) (emptyAccumulator @_ @_ @_ @_ @d fs) (noIVCProof fs)

ivcIterate :: forall f i p m c (d :: Natural) k a .
    ( SpecialSoundProtocol f i p m c d k a
    , Ring f
    , HomomorphicCommit m c
    , RandomOracle (i f) f
    , RandomOracle c f
    , KnownNat k
    , AccumulatorScheme f i m c d k (FiatShamir (CommitOpen a))
    ) => FiatShamir (CommitOpen a) -> IVCResult f i m c d k -> p f -> IVCResult f i m c d k
ivcIterate fs (IVCResult pi0 _ acc0 _) witness =
    let
        narkIP@(NARKInstanceProof pi (NARKProof cs _)) = narkInstanceProof @_ @_ @_ @_ @_ @d fs pi0 witness
        (acc, pf) = Acc.prover fs acc0 narkIP
        proof = IVCProof (acc0^.x) pf
    in
        IVCResult pi cs acc proof

ivcVerify :: forall f i m c d k a .
    ( AccumulatorScheme f i m c d k a
    ) => a -> IVCResult f i m c d k -> ((f, i f, Vector (k-1) f, Vector k c, c), (Vector k c, c))
ivcVerify a IVCResult {..} =
    let
        pi            = ivcInstance
        cs            = ivcCommits
        acc           = ivcAccumulator
        IVCProof {..} = ivcProof
        accX          = acc^.x
        accX0         = ivcpAccumulatorInstance
        pf            = ivcpAccumulationProof
    in
        ( Acc.verifier @f @i @m @c @d @k @a pi cs accX0 accX pf
        , decider @f @i @m @c @d @k @a a acc
        )
