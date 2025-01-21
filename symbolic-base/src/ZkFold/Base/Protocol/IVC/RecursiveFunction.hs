{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant ^." #-}

module ZkFold.Base.Protocol.IVC.RecursiveFunction where

import           Control.DeepSeq                            (NFData)
import           Data.Binary                                (Binary)
import           Data.Distributive                          (Distributive (..))
import           Data.Functor.Rep                           (Representable (..), collectRep, distributeRep, mzipWithRep)
import           Data.These                                 (These (..))
import           Data.Zip                                   (Semialign (..), Zip (..))
import           GHC.Generics                               (Generic, Generic1, Par1)
import           Prelude                                    (Foldable, Functor, Show, Traversable, fmap, type (~), ($))

import           ZkFold.Base.Algebra.Basic.Class            (FiniteField, FromConstant (..), Scale, zero, (*), (+), (-))
import           ZkFold.Base.Algebra.Basic.Number           (KnownNat, type (+), type (-))
import           ZkFold.Base.Data.Orphans                   ()
import           ZkFold.Base.Data.Package                   (packed, unpacked)
import           ZkFold.Base.Data.Vector                    (Vector)
import           ZkFold.Base.Protocol.IVC.Accumulator       hiding (pi, x)
import           ZkFold.Base.Protocol.IVC.AccumulatorScheme (AccumulatorScheme (..), accumulatorScheme)
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Base.Protocol.IVC.Predicate         (FunctorAssumptions, Predicate (..), PredicateFunction,
                                                             predicate)
import           ZkFold.Symbolic.Class                      (Arithmetic, Symbolic (..))
import           ZkFold.Symbolic.Data.Bool                  (Bool (..))
import           ZkFold.Symbolic.Data.Class                 (SymbolicData (..))
import           ZkFold.Symbolic.Data.Conditional           (Conditional (..))
import           ZkFold.Symbolic.Data.FieldElement          (FieldElement (..))
import           ZkFold.Symbolic.Data.Input                 (SymbolicInput)
import           ZkFold.Symbolic.Data.Payloaded             (Payloaded (..))

-- | Public input to the recursive function
data RecursiveI i f = RecursiveI (i f) f
    deriving (Generic, Generic1, Show, NFData, Functor, Foldable, Traversable)

instance Semialign i => Semialign (RecursiveI i) where
    alignWith f (RecursiveI x h) (RecursiveI y h') = RecursiveI (alignWith f x y) (f (These h h'))

instance Zip i => Zip (RecursiveI i) where
    zipWith f (RecursiveI x h) (RecursiveI y h') = RecursiveI (zipWith f x y) (f h h')

instance Representable i => Distributive (RecursiveI i) where
    distribute = distributeRep
    collect = collectRep

instance Representable i => Representable (RecursiveI i)

instance (SymbolicData f, SymbolicData (i f), Context f ~ Context (i f), Support f ~ Support (i f)) => SymbolicData (RecursiveI i f)

instance (SymbolicInput f, SymbolicInput (i f), Context f ~ Context (i f)) => SymbolicInput (RecursiveI i f)

instance {-# INCOHERENT #-} (Functor i, FromConstant a (FieldElement ctx)) => FromConstant (RecursiveI i a) (RecursiveI i (FieldElement ctx)) where
    fromConstant (RecursiveI x h) = RecursiveI (fmap fromConstant x) (fromConstant h)

instance (Symbolic ctx, Traversable i, Representable i) => Conditional (Bool ctx) (RecursiveI i (FieldElement ctx)) where
    bool x y b =
        let
            x' = packed $ fmap fromFieldElement x
            y' = packed $ fmap fromFieldElement y
        in fmap FieldElement $ unpacked $ bool x' y' b

-- | Payload to the recursive function
data RecursiveP d k i p c f = RecursiveP (p f) (Vector k (c f)) (AccumulatorInstance k (RecursiveI i) c f) f (Vector (d-1) (c f))
    deriving (Generic, Generic1, Functor, Foldable, Traversable)

instance (KnownNat (d-1), KnownNat (k-1), KnownNat k, Representable i, Representable p, Representable c) => Distributive (RecursiveP d k i p c) where
    distribute = distributeRep
    collect = collectRep

instance (KnownNat (d-1), KnownNat (k-1), KnownNat k, Representable i, Representable p, Representable c) => Representable (RecursiveP d k i p c)

--------------------------------------------------------------------------------

type RecursiveFunctionAssumptions algo a d k i p c f =
    ( HashAlgorithm algo
    , Arithmetic a
    , Binary a
    , KnownNat (d-1)
    , KnownNat (d+1)
    , k ~ 1 -- TODO: This should be generalized once we support multi-round special-sound protocols
    , FunctorAssumptions i
    , Zip i
    , FunctorAssumptions p
    , FunctorAssumptions c
    , c ~ Par1
    , FiniteField f
    , FromConstant a f
    , Scale a f
    )

type RecursiveFunction algo a d k i p c = forall ctx f . RecursiveFunctionAssumptions algo a d k i p c f
    => RecursiveI i (FieldElement ctx) -> Payloaded (RecursiveP d k i p c) ctx -> RecursiveI i (FieldElement ctx)

-- | Transform a step function into a recursive function
recursiveFunction :: forall algo a d k i p c f . RecursiveFunctionAssumptions algo a d k i p c f
    => PredicateFunction a i p
    -> RecursiveI i f
    -> RecursiveP d k i p c f
    -> RecursiveI i f
recursiveFunction func z@(RecursiveI x _) (RecursiveP u piX accX flag pf) =
    let
        pRec :: Predicate a (RecursiveI i) (RecursiveP d k i p c)
        pRec = predicate (recursiveFunction @algo @a func)

        accScheme :: AccumulatorScheme d k a (RecursiveI i) c
        accScheme = accumulatorScheme @algo pRec

        x' :: i f
        x' = func x u

        accX' :: AccumulatorInstance k (RecursiveI i) c f
        accX' = verifier accScheme z piX accX pf

        h :: f
        h = oracle @algo accX'
    in
        mzipWithRep (\v1 v2 -> v1 + (v2-v1)*flag) (RecursiveI x zero) (RecursiveI x' h)
