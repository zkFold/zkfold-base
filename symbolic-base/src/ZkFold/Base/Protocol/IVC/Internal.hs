{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant ^." #-}

module ZkFold.Base.Protocol.IVC.Internal where

import           Control.DeepSeq                            (NFData)
import           Control.Lens                               ((^.))
import           Control.Lens.Combinators                   (makeLenses)
import           Data.Functor.Rep                           (Representable (..))
import           Data.Kind                                  (Type)
import           Data.Type.Equality                         (type (~))
import           Data.Zip                                   (Zip (..), unzip)
import           GHC.Generics                               (Generic)
import           Prelude                                    (const, ($))
import qualified Prelude                                    as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number           (KnownNat, Natural, type (-))
import           ZkFold.Base.Data.Vector                    (Vector, empty, singleton)
import           ZkFold.Base.Protocol.IVC.Accumulator       hiding (pi)
import qualified ZkFold.Base.Protocol.IVC.AccumulatorScheme as Acc
import           ZkFold.Base.Protocol.IVC.AlgebraicMap      (AlgebraicMap)
import           ZkFold.Base.Protocol.IVC.Commit            (HomomorphicCommit)
import           ZkFold.Base.Protocol.IVC.CommitOpen
import           ZkFold.Base.Protocol.IVC.FiatShamir
import           ZkFold.Base.Protocol.IVC.NARK              (NARKInstanceProof (..), NARKProof (..))
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Base.Protocol.IVC.RecursiveFunction (RecursiveI (..), RecursiveP (..))
import           ZkFold.Base.Protocol.IVC.SpecialSound      (SpecialSoundProtocol (..))

-- | The recursion circuit satisfiability proof.
data IVCProof m c k
    = IVCProof
    { _proofX :: Vector k c
    -- ^ The commitment to the witness of the recursion circuit satisfiability proof.
    , _proofW :: Vector k m
    -- ^ The witness of the recursion circuit satisfiability proof.
    } deriving (GHC.Generics.Generic)

deriving instance (P.Show m, P.Show c) => P.Show (IVCProof m c k)
deriving instance (NFData m, NFData c) => NFData (IVCProof m c k)

noIVCProof :: forall m c k f .
    ( m ~ [f]
    , AdditiveMonoid f
    , AdditiveMonoid c
    , KnownNat k
    ) => IVCProof m c k
noIVCProof = IVCProof (tabulate $ const zero) (tabulate $ const zero)

-- | The current result of recursion together with the first iteration flag,
-- the corresponding accumulator, and the recursion circuit satisfiability proof.
data IVCResult f i m c k
    = IVCResult
    { _z     :: i f
    , _acc   :: Accumulator i m c k f
    , _proof :: IVCProof m c k
    , _flag  :: f
    } deriving (GHC.Generics.Generic)

makeLenses ''IVCResult

deriving instance (P.Show f, P.Show (i f), P.Show m, P.Show c) => P.Show (IVCResult f i m c k)
deriving instance (NFData f, NFData (i f), NFData m, NFData c) => NFData (IVCResult f i m c k)

type IVCAssumptions f i p m c d k a algo =
    ( SpecialSoundProtocol f i p m c d k a
    , SpecialSoundProtocol f (RecursiveI i c k) (RecursiveP i p c d k) m c d k a
    , Representable i
    , HashAlgorithm algo f
    , m ~ [f]
    , HomomorphicCommit m c
    , RandomOracle algo (i f) f
    , RandomOracle algo c f
    , KnownNat (k-1)
    , KnownNat k
    , AlgebraicMap f i d a
    , Acc.AccumulatorScheme f i m c d k (FiatShamir algo (CommitOpen a))
    )

-- | Create the first IVC result
-- 
-- It differs from the rest of the iterations as we don't have anything accumulated just yet.
ivcSetup :: forall f i p m c d k a algo . IVCAssumptions f i p m c d k a algo
    => FiatShamir algo (CommitOpen a)
    -> i f
    -> p f
    -> IVCResult f i m c k
ivcSetup fs x0 witness =
    let
        x1 = input @_ @_ @_ @(Vector k (m, c)) @c @d @1 fs x0 witness
    in
        IVCResult x1 (emptyAccumulator @f @i @m @c @d @k fs) (noIVCProof @m @c @k) zero

ivcProve :: forall f i p m c (d :: Natural) k a algo . IVCAssumptions f i p m c d k a algo
    => FiatShamir algo (CommitOpen a)
    -> IVCResult f i m c k
    -> p f
    -> IVCResult f i m c k
ivcProve fs res@(IVCResult _ _ (IVCProof cs ms) _) witness =
    let
        narkIP = NARKInstanceProof (res^.z) (NARKProof cs ms)
        (acc', pf) = Acc.prover @_ @_ @_ @_ @d fs (res^.acc) narkIP

        payload = RecursiveP (res^.z) witness one (res^.acc^.x) cs pf
        -- TODO: change to the original protocol's input
        RecursiveI pi _ = input @f @_ @_ @(Vector k (m, c)) @c @d @1 fs (RecursiveI (res^.z) (acc'^.x)) payload
        -- TODO: change Fiat-Shamired protocol for a one-round protocol
        (ms', cs') = unzip $ prover @f @(RecursiveI i c k) @_ @_ @c @d @1 fs (RecursiveI (res^.z) (res^.acc^.x)) payload (oracle @algo (res^.z)) 0
        ivcProof = IVCProof cs' ms'
    in
        IVCResult pi acc' ivcProof one

ivcVerify :: forall f i (p :: Type -> Type) m c d k a algo . IVCAssumptions f i p m c d k a algo
    => FiatShamir algo (CommitOpen a)
    -> IVCResult f i m c k
    -> (VerifierOutput f (RecursiveI i c k) (RecursiveP i p c d k) (Vector k (m, c)) c d 1 (FiatShamir algo (CommitOpen a)), (Vector k c, c))
ivcVerify fs res@(IVCResult _ _ (IVCProof cs ms) _) =
    let
    in
        -- TODO: change Fiat-Shamired protocol for a one-round protocol
        ( verifier @f @(RecursiveI i c k) @(RecursiveP i p c d k) @(Vector k (m, c)) @c @d @1
            fs (RecursiveI (res^.z) (res^.acc^.x)) (singleton $ zip ms cs) empty
        , Acc.decider @f @i @m @c @d @k fs (res^.acc)
        )
