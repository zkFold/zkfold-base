{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TypeOperators  #-}

module ZkFold.Base.Protocol.IVC.Internal where

import           Control.DeepSeq                            (NFData)
import           Control.Lens                               ((^.))
import           Data.Functor.Rep                           (Representable (..))
import           Data.Type.Equality                         (type (~))
import           GHC.Generics                               (Generic)
import           Prelude                                    (const, ($))
import qualified Prelude                                    as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number           (KnownNat, Natural, type (-))
import           ZkFold.Base.Data.Vector                    (Vector)
import           ZkFold.Base.Protocol.IVC.Accumulator       hiding (pi)
import qualified ZkFold.Base.Protocol.IVC.AccumulatorScheme as Acc
import           ZkFold.Base.Protocol.IVC.AlgebraicMap      (AlgebraicMap)
import           ZkFold.Base.Protocol.IVC.Commit            (HomomorphicCommit)
import           ZkFold.Base.Protocol.IVC.CommitOpen
import           ZkFold.Base.Protocol.IVC.FiatShamir
import           ZkFold.Base.Protocol.IVC.NARK              (NARKInstanceProof (..), NARKProof (..),
                                                                   narkInstanceProof)
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Base.Protocol.IVC.SpecialSound      (SpecialSoundProtocol (..))

data IVCProof f i m c d k
    = IVCProof
    { ivcpAccumulatorInstance :: AccumulatorInstance f i c k
    , ivcpAccumulationProof   :: Vector (d-1) c
    } deriving (GHC.Generics.Generic)

deriving instance (P.Show f, P.Show (i f), P.Show m, P.Show c) => P.Show (IVCProof f i m c d k)
deriving instance (NFData f, NFData (i f), NFData m, NFData c) => NFData (IVCProof f i m c d k)

noIVCProof :: forall f i m c d k a algo .
    ( Representable i
    , m ~ [f]
    , HomomorphicCommit m c
    , KnownNat (d-1)
    , KnownNat (k-1)
    , KnownNat k
    , AlgebraicMap f i d a
    ) => FiatShamir algo (CommitOpen a) -> IVCProof f i m c d k
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

ivcSetup :: forall f i m c (d :: Natural) k a algo .
    ( Representable i
    , m ~ [f]
    , HomomorphicCommit m c
    , KnownNat (d-1)
    , KnownNat (k-1)
    , KnownNat k
    , AlgebraicMap f i d a
    ) => FiatShamir algo (CommitOpen a) -> i f -> IVCResult f i m c d k
ivcSetup fs pi0 = IVCResult pi0 (tabulate $ const zero) (emptyAccumulator @_ @_ @_ @_ @d fs) (noIVCProof fs)

ivcProve :: forall f i p m c (d :: Natural) k a algo .
    ( SpecialSoundProtocol f i p m c d k a
    , HomomorphicCommit m c
    , HashAlgorithm algo f
    , RandomOracle algo (i f) f
    , RandomOracle algo c f
    , KnownNat k
    , Acc.AccumulatorScheme f i m c d k (FiatShamir algo (CommitOpen a))
    ) => FiatShamir algo (CommitOpen a) -> IVCResult f i m c d k -> p f -> IVCResult f i m c d k
ivcProve fs (IVCResult pi0 _ acc0 _) witness =
    let
        narkIP@(NARKInstanceProof pi (NARKProof cs _)) = narkInstanceProof @_ @_ @_ @_ @_ @d fs pi0 witness
        (acc, pf) = Acc.prover fs acc0 narkIP
        proof = IVCProof (acc0^.x) pf
    in
        IVCResult pi cs acc proof

ivcVerify :: forall f i m c d k a .
    ( Acc.AccumulatorScheme f i m c d k a
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
        , Acc.decider @f @i @m @c @d @k @a a acc
        )
