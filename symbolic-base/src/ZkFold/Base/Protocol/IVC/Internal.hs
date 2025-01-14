{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveAnyClass      #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeOperators       #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant ^." #-}

module ZkFold.Base.Protocol.IVC.Internal where

import           Control.DeepSeq                            (NFData)
import           Control.Lens                               ((^.), Traversable)
import           Control.Lens.Combinators                   (makeLenses)
import           Data.Functor.Rep                           (Representable (..))
import           Data.Zip                                   (Zip (..), unzip)
import           GHC.Generics                               (Generic, (:.:) (..), Par1)
import           Prelude                                    (Functor, Foldable, Show, fmap, const, id, foldl, error, ($))
import qualified Prelude                                    as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number           (KnownNat, value)
import           ZkFold.Base.Data.Package                   (unpacked)
import           ZkFold.Base.Data.Vector                    (Vector, head, tail)
import           ZkFold.Base.Protocol.IVC.Accumulator       hiding (pi)
import qualified ZkFold.Base.Protocol.IVC.AccumulatorScheme as Acc
import           ZkFold.Base.Protocol.IVC.AccumulatorScheme (AccumulatorScheme, accumulatorScheme)
import           ZkFold.Base.Protocol.IVC.CommitOpen        (commitOpen)
import           ZkFold.Base.Protocol.IVC.FiatShamir
import           ZkFold.Base.Protocol.IVC.NARK              (NARKInstanceProof (..), NARKProof (..))
import           ZkFold.Base.Protocol.IVC.Predicate         (StepFunction, Predicate (..), predicate)
import           ZkFold.Base.Protocol.IVC.RecursiveFunction
import           ZkFold.Base.Protocol.IVC.SpecialSound      (specialSoundProtocol)
import           ZkFold.Symbolic.Class                      (Symbolic(..), embedW)
import           ZkFold.Symbolic.Data.Bool                  (Bool, BoolType (..), all)
import           ZkFold.Symbolic.Data.Eq                    (Eq (..))
import           ZkFold.Symbolic.Data.FieldElement          (FieldElement (..))
import           ZkFold.Symbolic.Data.Payloaded             (Payloaded (..))

-- | The recursion circuit satisfiability proof.
data IVCProof k c f
    = IVCProof
    { _proofX :: Vector k (c f)
    -- ^ The commitment to the witness of the recursion circuit satisfiability proof.
    , _proofW :: Vector k [f]
    -- ^ The witness of the recursion circuit satisfiability proof.
    } deriving (GHC.Generics.Generic, Functor, Foldable, Traversable, Show, NFData)

makeLenses ''IVCProof

-- | The current result of recursion together with the first iteration flag,
-- the corresponding accumulator, and the recursion circuit satisfiability proof.
data IVCResult k i c f
    = IVCResult
    { _z     :: RecursiveI i f
    , _acc   :: Accumulator k (RecursiveI i) c f
    , _proof :: IVCProof k c f
    } deriving (GHC.Generics.Generic, Functor, Foldable, Traversable, Show, NFData)

makeLenses ''IVCResult

ivc :: forall algo a d k i p c ctx n .
    ( RecursiveFunctionAssumptions algo a d k i p c ctx
    , Eq (Bool ctx) (Par1 (FieldElement ctx))
    , KnownNat n
    )
    => StepFunction a i p
    -> i a
    -> Payloaded (Vector n :.: p) ctx
    -> (Bool ctx, AccumulatorInstance k (RecursiveI i) c (FieldElement ctx))
ivc f x0 (Payloaded (Comp1 ps)) =
    let
        pRec :: Predicate (RecursiveI i) (RecursiveP d k i p c) ctx
        pRec = predicate $ recursiveFunction @algo f (RecursiveI x0 zero)

        protocol :: FiatShamir k (RecursiveI i) (RecursiveP d k i p c) c ctx
        protocol = fiatShamir @algo $ commitOpen $ specialSoundProtocol @d pRec

        accScheme :: AccumulatorScheme d k (RecursiveI i) c ctx
        accScheme = accumulatorScheme @algo @d pRec id id

        ivcProve :: Haskell.Bool -> IVCResult k i c (WitnessField ctx) -> p (WitnessField ctx) -> IVCResult k i c (WitnessField ctx)
        ivcProve baseCase res witness =
            let
                narkIP :: NARKInstanceProof k (RecursiveI i) c ctx
                narkIP = NARKInstanceProof (res^.z) (NARKProof (res^.proof^.proofX) (res^.proof^.proofW))

                (acc', pf) = if baseCase
                    then (emptyAccumulator, tabulate (const zero))
                    else Acc.prover accScheme (res^.acc) narkIP

                payload :: RecursiveP d k i p c (WitnessField ctx)
                payload = RecursiveP witness (res^.proof^.proofX) (res^.acc^.x) one pf

                z' :: RecursiveI i (WitnessField ctx)
                z' = predicateWitness pRec (res^.z) payload

                (messages, commits) = unzip $ prover protocol (res^.z) payload

                ivcProof :: IVCProof k c (WitnessField ctx)
                ivcProof = IVCProof commits messages
            in
                IVCResult z' acc' ivcProof

        ivcVerify :: IVCResult k i c (FieldElement ctx) -> Bool ctx
        ivcVerify res =
            let
                (vs1, vs2) = verifier protocol (res^.z) (zip (res^.proof^.proofW) (res^.proof^.proofX))
            in
                all (== zero) vs1 && all (== zero) vs2

        res0 :: IVCResult k i c (WitnessField ctx)
        res0 = IVCResult (RecursiveI (fmap fromConstant x0) zero) emptyAccumulator (IVCProof (tabulate $ const zero) (tabulate $ const []))

        setup :: IVCResult k i c (WitnessField ctx)
        setup = ivcProve true res0 (head ps)

        prove :: IVCResult k i c (WitnessField ctx) -> p (WitnessField ctx) -> IVCResult k i c (WitnessField ctx)
        prove = ivcProve false

        result :: IVCResult k i c (FieldElement ctx)
        result = fmap FieldElement $ unpacked $ embedW $ if value @n == 0
            then error "ivc: empty payload"
            else foldl prove setup (tail ps)
    in
        (ivcVerify result, result^.acc^.x)
