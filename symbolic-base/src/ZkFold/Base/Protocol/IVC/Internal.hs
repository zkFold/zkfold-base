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
import           Data.Type.Equality                         (type (~))
import           Data.Zip                                   (Zip (..), unzip)
import           GHC.Generics                               (Generic, U1, (:*:), (:.:) (..))
import           Prelude                                    (Functor, Foldable, Show, fmap, const, id, foldl, error, ($), (<$>))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number           (KnownNat, value)
import           ZkFold.Base.Data.Package                   (unpacked)
import           ZkFold.Base.Data.Vector                    (Vector, singleton, head, tail)
import           ZkFold.Base.Protocol.IVC.Accumulator       hiding (pi)
import qualified ZkFold.Base.Protocol.IVC.AccumulatorScheme as Acc
import           ZkFold.Base.Protocol.IVC.AccumulatorScheme (AccumulatorScheme, accumulatorScheme)
import           ZkFold.Base.Protocol.IVC.Commit            (HomomorphicCommit)
import           ZkFold.Base.Protocol.IVC.CommitOpen
import           ZkFold.Base.Protocol.IVC.FiatShamir
import           ZkFold.Base.Protocol.IVC.NARK              (NARKInstanceProof (..), NARKProof (..))
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Base.Protocol.IVC.Predicate         (StepFunction, Predicate (..), predicate)
import           ZkFold.Base.Protocol.IVC.RecursiveFunction
import           ZkFold.Base.Protocol.IVC.SpecialSound      (SpecialSoundProtocol (..), specialSoundProtocol,
                                                             specialSoundProtocol')
import           ZkFold.Symbolic.Class                      (Symbolic(..), embedW)
import           ZkFold.Symbolic.Compiler                   (ArithmeticCircuit)
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
    { _z     :: i f
    , _acc   :: Accumulator k (RecursiveI i) c f
    , _proof :: IVCProof k c f
    } deriving (GHC.Generics.Generic, Functor, Foldable, Traversable, Show, NFData)

makeLenses ''IVCResult

-- | Create the first IVC result
--
-- It differs from the rest of the iterations as we don't have anything accumulated just yet.
ivcSetup :: forall algo a d k i p c ctx w ctx1.
    ( ctx1 ~ ArithmeticCircuit a (RecursiveI i :*: RecursiveP d k i p c) U1
    , RecursiveFunctionAssumptions algo a d k i p c ctx1
    , RecursiveFunctionAssumptions algo a d k i p c ctx
    , WitnessField ctx ~ w
    , Field w
    , HomomorphicCommit [w] (c w)
    )
    => StepFunction i p
    -> i a
    -> p w
    -> IVCResult k i c w
ivcSetup f x0 witness =
    let
        p :: Predicate i p ctx
        p = predicate f

        z' :: i w
        z' = predicateWitness p (fromConstant <$> x0) witness

        fRec :: RecursiveFunction algo a d k i p c
        fRec = recursiveFunction @algo @a @d @k @i @p @c @ctx f (RecursiveI x0 zero)

        pRec :: Predicate (RecursiveI i) (RecursiveP d k i p c) ctx
        pRec = recursivePredicate @algo fRec

        acc0 :: Accumulator k (RecursiveI i) c w
        acc0 = emptyAccumulator @d pRec

        input :: RecursiveI i w
        input = RecursiveI (fromConstant <$> x0) (oracle @algo $ acc0^.x)

        payload :: RecursiveP d k i p c w
        payload = RecursiveP witness (tabulate (const zero)) (acc0^.x) zero (tabulate (const zero))

        protocol :: FiatShamir k (RecursiveI i) (RecursiveP d k i p c) c [w] [w] w
        protocol = fiatShamir @algo $ commitOpen $ specialSoundProtocol @d pRec

        (messages, commits) = unzip $ prover protocol input payload zero 0
    in IVCResult z' acc0 (IVCProof commits messages)

ivcProve :: forall algo a d k i p c ctx w ctx1.
    ( ctx1 ~ ArithmeticCircuit a (RecursiveI i :*: RecursiveP d k i p c) U1
    , RecursiveFunctionAssumptions algo a d k i p c ctx1
    , RecursiveFunctionAssumptions algo a d k i p c ctx
    , WitnessField ctx ~ w
    , Field w
    , HomomorphicCommit [w] (c w)
    , Scale w (c w)
    )
    => StepFunction i p
    -> i a
    -> IVCResult k i c w
    -> p w
    -> IVCResult k i c w
ivcProve f x0 res witness =
    let
        p :: Predicate i p ctx
        p = predicate f

        z' :: i w
        z' = predicateWitness p (res^.z) witness

        pRec :: Predicate (RecursiveI i) (RecursiveP d k i p c) ctx
        pRec = recursivePredicate @algo $ recursiveFunction @algo @a @d @k @i @p @c @ctx f (RecursiveI x0 zero)

        input :: RecursiveI i w
        input = RecursiveI (res^.z) (oracle @algo $ res^.acc^.x)

        messages :: Vector k [w]
        messages = res^.proof^.proofW

        commits :: Vector k (c w)
        commits = res^.proof^.proofX

        narkIP :: NARKInstanceProof k (RecursiveI i) c w
        narkIP = NARKInstanceProof input (NARKProof commits messages)

        accScheme :: AccumulatorScheme d k (RecursiveI i) c w
        accScheme = accumulatorScheme @algo @d pRec id

        (acc', pf) = Acc.prover accScheme (res^.acc) narkIP

        payload :: RecursiveP d k i p c w
        payload = RecursiveP witness commits (res^.acc^.x) one pf

        protocol :: FiatShamir k (RecursiveI i) (RecursiveP d k i p c) c [w] [w] w
        protocol = fiatShamir @algo $ commitOpen $ specialSoundProtocol @d pRec

        (messages', commits') = unzip $ prover protocol input payload zero 0

        ivcProof :: IVCProof k c w
        ivcProof = IVCProof commits' messages'
    in
        IVCResult z' acc' ivcProof

ivcVerify :: forall algo a d k i p c ctx f ctx1 .
    ( ctx1 ~ ArithmeticCircuit a (RecursiveI i :*: RecursiveP d k i p c) U1
    , RecursiveFunctionAssumptions algo a d k i p c ctx1
    , RecursiveFunctionAssumptions algo a d k i p c ctx
    , FieldElement ctx ~ f
    , Eq (Bool ctx) (c f)
    )
    => StepFunction i p
    -> i a
    -> IVCResult k i c f
    -> Bool ctx
ivcVerify f x0 res =
    let
        pRec :: Predicate (RecursiveI i) (RecursiveP d k i p c) ctx
        pRec = recursivePredicate @algo $ recursiveFunction @algo @a @d @k @i @p @c @ctx f (RecursiveI x0 zero)

        input :: RecursiveI i f
        input = RecursiveI (res^.z) (oracle @algo $ res^.acc^.x)

        messages :: Vector k [f]
        messages = res^.proof^.proofW

        commits :: Vector k (c f)
        commits = res^.proof^.proofX

        protocol :: FiatShamir k (RecursiveI i) (RecursiveP d k i p c) c [f] [f] f
        protocol = fiatShamir @algo $ commitOpen $ specialSoundProtocol' @d pRec

        (vs1, vs2) = verifier protocol input (singleton $ zip messages commits) zero
    in all (== zero) vs1 && all (== zero) vs2

ivc :: forall algo a d k i p c ctx w n ctx1 .
    ( ctx1 ~ ArithmeticCircuit a (RecursiveI i :*: RecursiveP d k i p c) U1
    , RecursiveFunctionAssumptions algo a d k i p c ctx1
    , RecursiveFunctionAssumptions algo a d k i p c ctx
    , WitnessField ctx ~ w
    , Field w
    , HomomorphicCommit [w] (c w)
    , Scale w (c w)
    , KnownNat n
    , Eq (Bool ctx) (c (FieldElement ctx))
    )
    => StepFunction i p
    -> i a
    -> Payloaded (Vector n :.: p) ctx
    -> (Bool ctx, AccumulatorInstance k (RecursiveI i) c (FieldElement ctx))
ivc f x0 (Payloaded (Comp1 ps)) =
    let
        setup :: IVCResult k i c w
        setup = ivcSetup @algo @_ @d @_ @_ @_ @_ @ctx f x0 (head ps)

        prove :: IVCResult k i c w -> p w -> IVCResult k i c w
        prove = ivcProve @algo @_ @d @_ @_ @_ @_ @ctx f x0

        res :: IVCResult k i c (FieldElement ctx)
        res = fmap FieldElement $ unpacked $ embedW $ if value @n == 0
            then error "ivc: empty payload"
            else foldl prove setup (tail ps)
    in
        (ivcVerify @algo @_ @d f x0 res, res^.acc^.x)
