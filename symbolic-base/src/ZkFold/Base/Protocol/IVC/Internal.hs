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
import           ZkFold.Base.Algebra.Basic.Number           (KnownNat, Natural, type (-), type (+))
import           ZkFold.Base.Data.Vector                    (Vector, empty, singleton)
import           ZkFold.Base.Protocol.IVC.Accumulator       hiding (pi)
import qualified ZkFold.Base.Protocol.IVC.AccumulatorScheme as Acc
import           ZkFold.Base.Protocol.IVC.AlgebraicMap      (algebraicMap)
import           ZkFold.Base.Protocol.IVC.Commit            (HomomorphicCommit)
import           ZkFold.Base.Protocol.IVC.CommitOpen
import           ZkFold.Base.Protocol.IVC.FiatShamir
import           ZkFold.Base.Protocol.IVC.NARK              (NARKInstanceProof (..), NARKProof (..))
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Base.Protocol.IVC.RecursiveFunction (RecursiveI (..), RecursiveP (..))
import           ZkFold.Base.Protocol.IVC.SpecialSound      (SpecialSoundProtocol (..), specialSoundProtocol)
import ZkFold.Base.Protocol.IVC.Predicate (Predicate (predicateEval))
import ZkFold.Base.Protocol.IVC.AccumulatorScheme (accumulatorScheme)
import ZkFold.Symbolic.Class (Arithmetic)

-- | The recursion circuit satisfiability proof.
data IVCProof k m c
    = IVCProof
    { _proofX :: Vector k c
    -- ^ The commitment to the witness of the recursion circuit satisfiability proof.
    , _proofW :: Vector k m
    -- ^ The witness of the recursion circuit satisfiability proof.
    } deriving (GHC.Generics.Generic)

deriving instance (P.Show m, P.Show c) => P.Show (IVCProof k m c)
deriving instance (NFData m, NFData c) => NFData (IVCProof k m c)

noIVCProof :: forall k m c f .
    ( KnownNat k
    , m ~ [f]
    , AdditiveMonoid c
    , AdditiveMonoid f
    ) => IVCProof k m c
noIVCProof = IVCProof (tabulate $ const zero) (tabulate $ const zero)

-- | The current result of recursion together with the first iteration flag,
-- the corresponding accumulator, and the recursion circuit satisfiability proof.
data IVCResult k i m c f
    = IVCResult
    { _z     :: i f
    , _acc   :: Accumulator k i m c f
    , _proof :: IVCProof k m c
    , _flag  :: f
    } deriving (GHC.Generics.Generic)

makeLenses ''IVCResult

deriving instance (P.Show f, P.Show (i f), P.Show m, P.Show c) => P.Show (IVCResult k i m c f)
deriving instance (NFData f, NFData (i f), NFData m, NFData c) => NFData (IVCResult k i m c f)

type IVCAssumptions algo d k a i p o m c f =
    ( --SpecialSoundProtocol f i p m c d k a
    -- , SpecialSoundProtocol f (RecursiveI i c k) (RecursiveP i p c d k) m c d k a
    Representable i
    , HashAlgorithm algo f
    , m ~ [f]
    , HomomorphicCommit m c
    , RandomOracle algo (i f) f
    , RandomOracle algo c f
    , KnownNat (d+1)
    , KnownNat (k-1)
    , KnownNat k
    , Arithmetic a
    , Ring f
    -- , Acc.AccumulatorScheme f i o m c d k
    )

-- | Create the first IVC result
-- 
-- It differs from the rest of the iterations as we don't have anything accumulated just yet.
ivcSetup :: forall algo d k a i p o m c . IVCAssumptions algo d k a i p o m c a
    => Predicate a i p
    -> i a
    -> p a
    -> IVCResult k i m c a
ivcSetup p x0 witness =
    let
        x1 = predicateEval p x0 witness
    in
        IVCResult x1 (emptyAccumulator @d p) noIVCProof zero

-- ivcProve :: forall algo d k a i p o m c f . IVCAssumptions algo d k a i p o m c f
--     => Predicate i p f
--     -> IVCResult k i m c f
--     -> p f
--     -> IVCResult k i m c f
-- ivcProve p res@(IVCResult _ _ (IVCProof cs ms) _) witness =
--     let
--         narkIP = NARKInstanceProof (res^.z) (NARKProof cs ms)
--         -- TODO: this must be an accumulator scheme for the recursive function
--         as = accumulatorScheme p
--         (acc', pf) = Acc.prover as (res^.acc) narkIP
--         -- TODO: this must be a protocol for the recursive function
--         sps = specialSoundProtocol p
--         -- payload = RecursiveP (res^.z) witness one (res^.acc^.x) cs pf
--         -- TODO: change to the original protocol's input
--         -- RecursiveI pi _ = predicateEval p (RecursiveI (res^.z) (acc'^.x)) payload
--         -- pi = predicateEval p (res^.z) witness
--         -- TODO: change Fiat-Shamired protocol for a one-round protocol
--         (ms', cs') = unzip $ prover p (RecursiveI (res^.z) (res^.acc^.x)) payload (oracle @algo (res^.z)) 0
--         ivcProof = IVCProof cs' ms'
--     in
--         IVCResult pi acc' ivcProof one

-- ivcVerify :: forall f i (p :: Type -> Type) m c d k a algo . IVCAssumptions f i p m c d k a algo
--     => FiatShamir algo (CommitOpen a)
--     -> IVCResult f i m c k
--     -> (VerifierOutput f (RecursiveI i c k) (RecursiveP i p c d k) (Vector k (m, c)) c d 1 (FiatShamir algo (CommitOpen a)), (Vector k c, c))
-- ivcVerify fs res@(IVCResult _ _ (IVCProof cs ms) _) =
--     let
--     in
--         -- TODO: change Fiat-Shamired protocol for a one-round protocol
--         ( verifier @f @(RecursiveI i c k) @(RecursiveP i p c d k) @(Vector k (m, c)) @c @d @1
--             fs (RecursiveI (res^.z) (res^.acc^.x)) (singleton $ zip ms cs) empty
--         , Acc.decider @f @i @m @c @d @k fs (res^.acc)
--         )
