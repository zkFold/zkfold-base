{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Redundant ^." #-}

module ZkFold.Base.Protocol.IVC.RecursiveFunction where

import           Control.DeepSeq                            (NFData)
import           Data.Distributive                          (Distributive (..))
import           Data.Functor.Rep                           (Representable (..), collectRep, distributeRep)
import           Data.These                                 (These (..))
import           Data.Zip                                   (Semialign (..), Zip (..))
import           GHC.Generics                               (Generic, Generic1, U1 (..), (:*:) (..))
import           Prelude                                    (Foldable, Functor, Show, Traversable, type (~), fmap, id, ($),
                                                             (.), (<$>))

import           ZkFold.Base.Algebra.Basic.Class            (Scale, FromConstant (..))
import           ZkFold.Base.Algebra.Basic.Number           (KnownNat, type (+), type (-))
import           ZkFold.Base.Algebra.Polynomials.Univariate (PolyVec)
import           ZkFold.Base.Data.Orphans                   ()
import           ZkFold.Base.Data.Package                   (packed, unpacked)
import           ZkFold.Base.Data.Vector                    (Vector)
import           ZkFold.Base.Protocol.IVC.Accumulator       hiding (pi, x)
import           ZkFold.Base.Protocol.IVC.AccumulatorScheme (AccumulatorScheme (..), accumulatorScheme)
import           ZkFold.Base.Protocol.IVC.Commit            (HomomorphicCommit)
import           ZkFold.Base.Protocol.IVC.Oracle
import           ZkFold.Base.Protocol.IVC.Predicate         (Predicate (..), PredicateAssumptions, PredicateCircuit,
                                                             predicate)
import           ZkFold.Base.Protocol.IVC.StepFunction      (FunctorAssumptions, StepFunction, StepFunctionAssumptions)
import           ZkFold.Symbolic.Class                      (Symbolic(..), embedW)
import           ZkFold.Symbolic.Compiler                   (ArithmeticCircuit, compileWith, guessOutput, hlmap)
import           ZkFold.Symbolic.Data.Bool                  (Bool (..))
import           ZkFold.Symbolic.Data.Class                 (SymbolicData (..))
import           ZkFold.Symbolic.Data.Conditional           (bool, Conditional)
import           ZkFold.Symbolic.Data.FieldElement          (FieldElement (FieldElement), fromFieldElement)
import           ZkFold.Symbolic.Data.Input                 (SymbolicInput)
import           ZkFold.Symbolic.Interpreter                (Interpreter (..))

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

instance (RandomOracle algo [f] f, RandomOracle algo (i f) f) => RandomOracle algo (RecursiveI i f) f

instance (SymbolicData f, SymbolicData (i f), Context f ~ Context (i f), Support f ~ Support (i f)) => SymbolicData (RecursiveI i f)

instance (SymbolicInput f, SymbolicInput (i f), Context f ~ Context (i f)) => SymbolicInput (RecursiveI i f)

-- | Payload to the recursive function
data RecursiveP d k i p c f = RecursiveP (p f) (Vector k (c f)) (AccumulatorInstance k (RecursiveI i) c f) f (Vector (d-1) (c f))
    deriving (Generic, Generic1, Functor, Foldable, Traversable)

instance (KnownNat (d-1), KnownNat (k-1), KnownNat k, Representable i, Representable p, Representable c) => Distributive (RecursiveP d k i p c) where
    distribute = distributeRep
    collect = collectRep

instance (KnownNat (d-1), KnownNat (k-1), KnownNat k, Representable i, Representable p, Representable c) => Representable (RecursiveP d k i p c)

--------------------------------------------------------------------------------

type RecursiveFunctionAssumptions algo d a i c f ctx =
    ( StepFunctionAssumptions a ctx
    , FieldElement ctx ~ f
    , RandomOracle algo [f] f
    , RandomOracle algo (i f) f
    , RandomOracle algo (c f) f
    , HomomorphicCommit [f] (c f)
    , Scale a f
    , Scale a (PolyVec f (d+1))
    , Scale f (c f)
    , FromConstant (RecursiveI i a) (RecursiveI i f)
    , Conditional (Bool ctx) (RecursiveI i f)
    )

type RecursiveFunction algo d k a i p c = forall f ctx . RecursiveFunctionAssumptions algo d a i c f ctx
    => RecursiveI i f -> RecursiveP d k i p c f -> RecursiveI i f

-- | Transform a step function into a recursive function
recursiveFunction :: forall algo d k a i p c ctx.
    ( PredicateAssumptions a i p
    , FunctorAssumptions c
    , KnownNat (d-1)
    , KnownNat (d+1)
    , KnownNat (k-1)
    , KnownNat k
    , Zip i
    , Symbolic ctx
    , BaseField ctx ~ a
    ) => StepFunction a i p -> RecursiveI i a -> RecursiveFunction algo d k a i p c
recursiveFunction func z0 =
    let
        -- A helper function to derive the accumulator scheme
        func' :: forall ctx' . StepFunctionAssumptions a ctx'
            => RecursiveI i (FieldElement ctx')
            -> RecursiveP d k i p c (FieldElement ctx')
            -> RecursiveI i (FieldElement ctx')
        func' (RecursiveI x h) (RecursiveP u _ _ _ _) = RecursiveI (func x u) h

        -- A helper predicate to derive the accumulator scheme
        pRec :: Predicate a (RecursiveI i) (RecursiveP d k i p c) ctx
        pRec = predicate @_ @_ @_ @ctx func'

        funcRecursive :: forall ctx' f . RecursiveFunctionAssumptions algo d a i c f ctx'
            => RecursiveI i (FieldElement ctx')
            -> RecursiveP d k i p c (FieldElement ctx')
            -> RecursiveI i (FieldElement ctx')
        funcRecursive z@(RecursiveI x _) (RecursiveP u piX accX flag pf) =
            let
                accScheme :: AccumulatorScheme d k (RecursiveI i) c (FieldElement ctx')
                accScheme = accumulatorScheme @algo pRec id

                x' :: i (FieldElement ctx')
                x' = func x u

                accX' :: AccumulatorInstance k (RecursiveI i) c (FieldElement ctx')
                accX' = verifier accScheme z piX accX pf

                h :: (FieldElement ctx')
                h = oracle @algo accX'
            in
                bool (fromConstant z0) (RecursiveI x' h) $ Bool $ fromFieldElement flag

    in funcRecursive

--------------------------------------------------------------------------------

type RecursivePredicateAssumptions algo d k a i p c =
    ( KnownNat (d-1)
    , KnownNat (k-1)
    , KnownNat k
    , PredicateAssumptions a i p
    , FunctorAssumptions c
    )

recursivePredicate :: forall algo d k a i p c ctx0 ctx1 ctx .
    ( RecursivePredicateAssumptions algo d k a i p c
    , RecursiveFunctionAssumptions algo d a i c (FieldElement ctx) ctx
    , ctx0 ~ Interpreter a
    , RecursiveFunctionAssumptions algo d a i c (FieldElement ctx0) ctx0
    , ctx1 ~ ArithmeticCircuit a (RecursiveI i :*: RecursiveP d k i p c) U1
    , RecursiveFunctionAssumptions algo d a i c (FieldElement ctx1) ctx1
    ) => RecursiveFunction algo d k a i p c -> Predicate a (RecursiveI i) (RecursiveP d k i p c) ctx
recursivePredicate func =
    let
        predicateEval :: (RecursiveI i) a -> (RecursiveP d k i p c) a -> (RecursiveI i) a
        predicateEval z u = runInterpreter $ func' (Interpreter z) (Interpreter u)

        predicateWitness :: (RecursiveI i) (WitnessField ctx) -> (RecursiveP d k i p c) (WitnessField ctx) -> (RecursiveI i) (WitnessField ctx)
        predicateWitness x' u' =
            let
                x :: (RecursiveI i) (FieldElement ctx)
                x = fmap FieldElement $ unpacked $ embedW x'

                u :: (RecursiveP d k i p c) (FieldElement ctx)
                u = fmap FieldElement $ unpacked $ embedW u'
            in
                witnessF . packed . fmap fromFieldElement $ func x u

        func' :: forall f ctx' . RecursiveFunctionAssumptions algo d a i c f ctx'
            => ctx' (RecursiveI i) -> ctx' (RecursiveP d k i p c) -> ctx' (RecursiveI i)
        func' x' u' =
            let
                x = FieldElement <$> unpacked x'
                u = FieldElement <$> unpacked u'
            in
                packed . fmap fromFieldElement $ func x u

        predicateCircuit :: PredicateCircuit a (RecursiveI i) (RecursiveP d k i p c)
        predicateCircuit =
            hlmap (U1 :*:) $
            compileWith @a guessOutput (\(i :*: p) U1 -> (U1 :*: U1 :*: U1, i :*: p :*: U1)) func'        
    in Predicate {..}
