{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE TypeOperators        #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant ^." #-}

module ZkFold.Base.Protocol.IVC.CycleFold where

import           Control.Lens                               ((^.))
import           Data.Functor.Rep                           (Representable (..))
import           Data.Zip                                   (Zip (..))
import           Prelude                                    (Functor, Traversable, type (~), fmap, ($),
                                                             (.), const)

import           ZkFold.Base.Algebra.Basic.Class            (Scale, FromConstant (..), zero)
import           ZkFold.Base.Algebra.Basic.Number           (KnownNat, type (+), type (-))
import           ZkFold.Base.Data.ByteString                (Binary)
import           ZkFold.Base.Data.Package                   (unpacked)
import           ZkFold.Base.Protocol.IVC.Accumulator
import           ZkFold.Base.Protocol.IVC.AccumulatorScheme (AccumulatorScheme (..), accumulatorScheme)
import           ZkFold.Base.Protocol.IVC.Commit            (HomomorphicCommit)
import           ZkFold.Base.Protocol.IVC.CommitOpen        (commitOpen)
import           ZkFold.Base.Protocol.IVC.FiatShamir        (FiatShamir, fiatShamir)
import           ZkFold.Base.Protocol.IVC.NARK              (NARKInstanceProof (..), NARKProof (..), narkInstanceProof)
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Base.Protocol.IVC.Predicate         (Predicate (..), FunctorAssumptions)
import           ZkFold.Base.Protocol.IVC.SpecialSound      (specialSoundProtocol)
import           ZkFold.Symbolic.Class                      (Symbolic(..), embedW)
import           ZkFold.Symbolic.Data.Bool                  (Bool (..))
import           ZkFold.Symbolic.Data.Conditional           (Conditional (..))
import           ZkFold.Symbolic.Data.Eq                    (Eq (..))
import           ZkFold.Symbolic.Data.FieldElement          (FieldElement (..))

type ForeignFunctionAssumptions algo a d k i p c ctx =
    ( Symbolic ctx
    , BaseField ctx ~ a
    , Binary (BaseField ctx)
    , HashAlgorithm algo
    , HomomorphicCommit [FieldElement ctx] (c (FieldElement ctx))
    , Scale (FieldElement ctx) (c (FieldElement ctx))
    , KnownNat (d-1)
    , KnownNat (d+1)
    , k ~ 1 -- TODO: This should be generalized once we support multi-round special-sound protocols
    , FunctorAssumptions i
    , FunctorAssumptions p
    , FunctorAssumptions c
    , Zip i
    )

accumulate :: forall algo a d k i p c w f ctx w' f' ctx' .
    ( ForeignFunctionAssumptions algo a d k i p c ctx'
    , Symbolic ctx
    , w ~ WitnessField ctx
    , f ~ FieldElement ctx
    , w' ~ WitnessField ctx'
    , f' ~ FieldElement ctx'
    , FromConstant a w'
    , Scale a w'
    , HomomorphicCommit [w'] (c w')
    , HomomorphicCommit [f'] (c f)
    , Scale f (c f)
    , Functor (NARKInstanceProof k i c)
    , Representable (Accumulator k i c)
    , Eq (Bool ctx) (AccumulatorInstance k i c f)
    , Conditional (Bool ctx) (Accumulator k i c f), Traversable (NARKInstanceProof 1 i c)
    )
    => Predicate i p ctx'
    -> (f -> f')
    -> (w' -> w)
    -> p w'
    -> Accumulator k i c w
    -> Accumulator k i c f
accumulate phi toForeignField fromForeignField u acc =
    let
        protocol :: FiatShamir k i p c [w'] [w'] w'
        protocol = fiatShamir @algo $ commitOpen $ specialSoundProtocol @d phi

        narkIP' :: NARKInstanceProof k i c w'
        narkIP' = narkInstanceProof protocol (tabulate $ const zero) u

        narkIP :: NARKInstanceProof k i c w
        narkIP = fmap fromForeignField narkIP'

        NARKInstanceProof pubi (NARKProof pi_x _) = eW narkIP

        accScheme :: AccumulatorScheme d k i c f
        accScheme = accumulatorScheme @algo phi toForeignField

        -- TODO: fix here
        (acc', pf) = prover accScheme (eW acc) (eW narkIP)

        eW :: Traversable t => t w -> t f
        eW = fmap FieldElement . unpacked . embedW

        b :: Bool ctx
        b = acc'^.x == verifier accScheme pubi pi_x (eW $ acc^.x) pf
    in
        bool (tabulate $ const zero) acc' b
