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
import           Data.Type.Equality                         (type (~))
import           Data.Zip                                   (Zip (..), unzip)
import           GHC.Generics                               (Generic)
import           Prelude                                    (const, ($))
import qualified Prelude                                    as P

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number           (KnownNat, type (-), type (+))
import           ZkFold.Base.Algebra.Polynomials.Univariate (PolyVec)
import           ZkFold.Base.Data.Vector                    (Vector, empty)
import           ZkFold.Base.Protocol.IVC.Accumulator       hiding (pi)
import qualified ZkFold.Base.Protocol.IVC.AccumulatorScheme as Acc
import           ZkFold.Base.Protocol.IVC.AccumulatorScheme (accumulatorScheme)
import           ZkFold.Base.Protocol.IVC.AlgebraicMap      (algebraicMap)
import           ZkFold.Base.Protocol.IVC.Commit            (HomomorphicCommit)
import           ZkFold.Base.Protocol.IVC.CommitOpen
import           ZkFold.Base.Protocol.IVC.FiatShamir
import           ZkFold.Base.Protocol.IVC.NARK              (NARKInstanceProof (..), NARKProof (..))
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Base.Protocol.IVC.Predicate         (Predicate (..))
import           ZkFold.Base.Protocol.IVC.SpecialSound      (SpecialSoundProtocol (..), specialSoundProtocol)
import           ZkFold.Symbolic.Class                      (Arithmetic)

-- | The recursion circuit satisfiability proof.
data IVCProof k c m f
    = IVCProof
    { _proofX :: Vector k (c f)
    -- ^ The commitment to the witness of the recursion circuit satisfiability proof.
    , _proofW :: Vector k m
    -- ^ The witness of the recursion circuit satisfiability proof.
    } deriving (GHC.Generics.Generic)

deriving instance (P.Show (c f), P.Show m) => P.Show (IVCProof k c m f)
deriving instance (NFData (c f), NFData m) => NFData (IVCProof k c m f)

noIVCProof :: forall k c m f .
    ( KnownNat k
    , AdditiveMonoid (c f)
    , m ~ [f]    
    , AdditiveMonoid f
    ) => IVCProof k c m f
noIVCProof = IVCProof (tabulate $ const zero) (tabulate $ const zero)

-- | The current result of recursion together with the first iteration flag,
-- the corresponding accumulator, and the recursion circuit satisfiability proof.
data IVCResult k i c m f
    = IVCResult
    { _z     :: i f
    , _acc   :: Accumulator k i c m f
    , _proof :: IVCProof k c m f
    , _flag  :: f
    } deriving (GHC.Generics.Generic)

makeLenses ''IVCResult

deriving instance (P.Show f, P.Show (i f), P.Show (c f), P.Show m) => P.Show (IVCResult k i c m f)
deriving instance (NFData f, NFData (i f), NFData (c f), NFData m) => NFData (IVCResult k i c m f)

type IVCAssumptions algo d k a i p c m o f =
    ( Representable i
    , Zip i
    , Representable p
    , HashAlgorithm algo f
    , m ~ [f]
    , HomomorphicCommit m (c f)
    , RandomOracle algo f f
    , RandomOracle algo (i f) f
    , RandomOracle algo (c f) f
    , KnownNat (d-1)
    , KnownNat (d+1)
    , k ~ 1
    , KnownNat (k-1)
    , KnownNat k
    , Arithmetic a
    , Field f
    , Scale a f
    , Scale a (c f)
    , Scale f (c f)
    , Scale a (PolyVec f (d+1))
    )

-- | Create the first IVC result
-- 
-- It differs from the rest of the iterations as we don't have anything accumulated just yet.
ivcSetup :: forall algo d k a i p o m c . IVCAssumptions algo d k a i p c m o a
    => Predicate a i p
    -> i a
    -> p a
    -> IVCResult k i c m a
ivcSetup p x0 witness =
    let
        x1 = predicateEval p x0 witness
    in
        IVCResult x1 (emptyAccumulator @d p) noIVCProof zero

ivcProve :: forall algo d k a i p c m o . IVCAssumptions algo d k a i p c m o a
    => Predicate a i p
    -> IVCResult k i c m a
    -> p a
    -> IVCResult k i c m a
ivcProve p res@(IVCResult _ _ (IVCProof cs ms) _) witness =
    let
        narkIP = NARKInstanceProof (res^.z) (NARKProof cs ms)

        -- TODO: this must be an accumulator scheme for the recursive function
        as = accumulatorScheme @algo @d p

        (acc', _) = Acc.prover as (res^.acc) narkIP

        -- TODO: this must be a protocol for the recursive function
        sps = fiatShamir @algo $ commitOpen $ specialSoundProtocol @d p

        -- input = RecursiveI (res^.z) (res^.acc^.x)
        -- payload = RecursiveP (res^.z) witness one (res^.acc^.x) cs pf
        
        (ms', cs') = unzip $ prover sps (res^.z) witness (oracle @algo (res^.z)) 0
        ivcProof = IVCProof cs' ms'

        pi = predicateEval p (res^.z) witness
    in
        IVCResult pi acc' ivcProof one

ivcVerify :: forall algo d k a i p c m o f . IVCAssumptions algo d k a i p c m o f
    => Predicate a i p
    -> IVCResult k i c m f
    -> ([f], (Vector k (c f), c f))
ivcVerify p res@(IVCResult _ _ (IVCProof _ ms) _) =
    let
        as = accumulatorScheme @algo @d p
    in
        -- TODO: this must be an algebraic map for the recursive function
        ( algebraicMap @d p (res^.z) ms empty one
        , Acc.decider as (res^.acc)
        )
