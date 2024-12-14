{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant ^." #-}

module ZkFold.Base.Protocol.IVC.RecursiveFunction where

import           Data.Distributive                          (Distributive (..))
import           Data.Functor.Rep                           (Representable (..), distributeRep, collectRep)
import           Data.Zip                                   (Zip)
import           GHC.Generics                               (Generic, Generic1, (:*:) (..), U1 (..))
import           Prelude                                    (Foldable, Traversable, type (~), Functor, fmap, (<$>), (.), ($))

import           ZkFold.Base.Algebra.Basic.Class            (Scale)
import           ZkFold.Base.Algebra.Basic.Number           (type (+), type (-), KnownNat)
import           ZkFold.Base.Algebra.Polynomials.Univariate (PolyVec)
import           ZkFold.Base.Data.Orphans                   ()
import           ZkFold.Base.Data.Package                   (unpacked, packed)
import           ZkFold.Base.Data.Vector                    (Vector)
import           ZkFold.Base.Protocol.IVC.Accumulator       hiding (pi, x)
import           ZkFold.Base.Protocol.IVC.AccumulatorScheme (AccumulatorScheme (..), accumulatorScheme)
import           ZkFold.Base.Protocol.IVC.Commit            (HomomorphicCommit)
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Base.Protocol.IVC.Predicate         (Predicate (..), PredicateAssumptions, PredicateCircuit, predicate)
import           ZkFold.Base.Protocol.IVC.StepFunction      (StepFunctionAssumptions, StepFunction, FunctorAssumptions)
import           ZkFold.Symbolic.Compiler                   (ArithmeticCircuit, guessOutput, compileWith, hlmap)
import           ZkFold.Symbolic.Data.Bool                  (Bool(..))
import           ZkFold.Symbolic.Data.Class                 (SymbolicData (..))
import           ZkFold.Symbolic.Data.Conditional           (bool)
import           ZkFold.Symbolic.Data.FieldElement          (FieldElement (FieldElement), fromFieldElement)
import           ZkFold.Symbolic.Data.Input                 (SymbolicInput)
import           ZkFold.Symbolic.Interpreter                (Interpreter (..))

-- | Public input to the recursive function
data RecursiveI k i c f = RecursiveI (i f) (AccumulatorInstance k i c f)
    deriving (Generic, Generic1, Functor, Foldable, Traversable)

instance (KnownNat (k-1), KnownNat k, Representable i, Representable c) => Distributive (RecursiveI k i c) where
    distribute = distributeRep
    collect = collectRep

instance (KnownNat (k-1), KnownNat k, Representable i, Representable c) => Representable (RecursiveI k i c)

instance (HashAlgorithm algo f, RandomOracle algo f f, RandomOracle algo (i f) f, RandomOracle algo (c f) f) => RandomOracle algo (RecursiveI k i c f) f

-- | Payload to the recursive function
data RecursiveP d k i p c f = RecursiveP (p f) f (Vector k (c f)) (Vector (d-1) (c f))
    deriving (Generic, Generic1, Functor, Foldable, Traversable)

instance (KnownNat (d-1), KnownNat k, Functor p, Representable p, Functor c, Representable c) => Distributive (RecursiveP d k i p c) where
    distribute = distributeRep
    collect = collectRep

instance (KnownNat (d-1), KnownNat k, Functor p, Representable p, Functor c, Representable c) => Representable (RecursiveP d k i p c)

type RecursiveFunctionAssumptions algo d k a i c f ctx =
    ( StepFunctionAssumptions a f ctx
    , SymbolicInput (i f)
    , Context (i f) ~ ctx
    , SymbolicInput (c f)
    , Context (c f) ~ ctx
    , KnownNat (d-1)
    , KnownNat (d+1)
    , KnownNat (k-1)
    , KnownNat k
    , Zip i
    , HashAlgorithm algo f
    , RandomOracle algo f f
    , RandomOracle algo (i f) f
    , RandomOracle algo (c f) f
    , HomomorphicCommit [f] (c f)
    , Scale a f
    , Scale a (PolyVec f (d+1))
    , Scale f (c f)
    )

type RecursiveFunction algo d k a i p c = forall f ctx . RecursiveFunctionAssumptions algo d k a i c f ctx
    => RecursiveI k i c f -> RecursiveP d k i p c f -> RecursiveI k i c f

-- | Transform a step function into a recursive function
recursiveFunction :: forall algo d k a i p c ctx0 ctx1.
    ( PredicateAssumptions a i p
    , ctx0 ~ Interpreter a
    , StepFunctionAssumptions a (FieldElement ctx0) ctx0
    , ctx1 ~ ArithmeticCircuit a (i :*: p) U1
    , StepFunctionAssumptions a (FieldElement ctx1) ctx1
    ) => StepFunction a i p -> RecursiveFunction algo d k a i p c
recursiveFunction func =
    let
        p = predicate func :: Predicate a i p

        funcRecursive :: forall f ctx . RecursiveFunctionAssumptions algo d k a i c f ctx
            => RecursiveI k i c f
            -> RecursiveP d k i p c f
            -> RecursiveI k i c f
        funcRecursive (RecursiveI x accX) (RecursiveP u flag piX pf) =
            let
                as = accumulatorScheme @algo p :: AccumulatorScheme d k i c [FieldElement ctx] (FieldElement ctx)

                x'     = func x u
                accX'  = verifier as x piX accX pf

                accX0  = emptyAccumulatorInstance @d p :: AccumulatorInstance k i c (FieldElement ctx)
                accX'' = bool accX0 accX' $ Bool $ fromFieldElement flag
            in
                RecursiveI x' accX''

    in funcRecursive

--------------------------------------------------------------------------------

type RecursivePredicateAssumptions algo d k a i p c =
    ( KnownNat (d-1)
    , KnownNat (k-1)
    , KnownNat k
    , PredicateAssumptions a i p
    , FunctorAssumptions c
    )

recursivePredicate :: forall algo d k a i p c ctx0 ctx1 .
    ( RecursivePredicateAssumptions algo d k a i p c
    , ctx0 ~ Interpreter a
    , RecursiveFunctionAssumptions algo d k a i c (FieldElement ctx0) ctx0
    , ctx1 ~ ArithmeticCircuit a (RecursiveI k i c :*: RecursiveP d k i p c) U1
    , RecursiveFunctionAssumptions algo d k a i c (FieldElement ctx1) ctx1
    ) => RecursiveFunction algo d k a i p c -> Predicate a (RecursiveI k i c) (RecursiveP d k i p c)
recursivePredicate func =
    let
        func' :: forall f ctx . RecursiveFunctionAssumptions algo d k a i c f ctx
            => ctx (RecursiveI k i c) -> ctx (RecursiveP d k i p c) -> ctx (RecursiveI k i c)
        func' x' u' =
            let
                x = FieldElement <$> unpacked x'
                u = FieldElement <$> unpacked u'
            in
                packed . fmap fromFieldElement $ func x u

        predicateEval :: (RecursiveI k i c) a -> (RecursiveP d k i p c) a -> (RecursiveI k i c) a
        predicateEval z u = runInterpreter $ func' (Interpreter z) (Interpreter u)

        predicateCircuit :: PredicateCircuit a (RecursiveI k i c) (RecursiveP d k i p c)
        predicateCircuit =
            hlmap (U1 :*:) $
            compileWith @a guessOutput (\(i :*: p) U1 -> (U1 :*: U1 :*: U1, i :*: p :*: U1)) func'
    in Predicate {..}