{-# LANGUAGE TypeOperators #-}

module ZkFold.Base.Protocol.IVC.Predicate where

import           Data.Binary                           (Binary)
import           GHC.Generics                          (U1 (..), (:*:) (..))
import           Prelude                               hiding (Num (..), drop, head, replicate, take, zipWith)

import           ZkFold.Base.Control.HApplicative      (HApplicative(..))
import           ZkFold.Base.Data.Package              (packed, unpacked)
import           ZkFold.Base.Protocol.IVC.StepFunction (FunctorAssumptions, StepFunction, StepFunctionAssumptions)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler              (ArithmeticCircuit, compileWith, guessOutput, hlmap)
import           ZkFold.Symbolic.Data.FieldElement     (FieldElement (..))
import           ZkFold.Symbolic.Interpreter           (Interpreter(..))
import           ZkFold.Symbolic.MonadCircuit          (MonadCircuit(..))

type PredicateEval a i p        = i a -> p a -> i a
type PredicateWitness a i p ctx = i (WitnessField ctx) -> p (WitnessField ctx) -> i (WitnessField ctx)
type PredicateCircuit a i p     = ArithmeticCircuit a (i :*: p) i U1

data Predicate a i p ctx = Predicate
    { predicateEval    :: PredicateEval a i p
    , predicateWitness :: PredicateWitness a i p ctx
    , predicateCircuit :: PredicateCircuit a i p
    }

type PredicateAssumptions a i p =
    ( Arithmetic a
    , Binary a
    , FunctorAssumptions i
    , FunctorAssumptions p
    )

predicate :: forall a i p ctx . (PredicateAssumptions a i p, Symbolic ctx, BaseField ctx ~ a)
    => StepFunction a i p -> Predicate a i p ctx
predicate func =
    let
        predicateEval :: i a -> p a -> i a
        predicateEval x u = runInterpreter $ func' (Interpreter x) (Interpreter u)

        predicateWitness :: i (WitnessField ctx) -> p (WitnessField ctx) -> i (WitnessField ctx)
        predicateWitness x' u' =
            let
                x :: i (FieldElement ctx)
                x =
                    fmap FieldElement $
                    unpacked $ fromCircuitF (hunit @ctx) $
                    const (traverse unconstrained x')

                u :: p (FieldElement ctx)
                u =
                    fmap FieldElement $
                    unpacked $ fromCircuitF (hunit @ctx) $
                    const (traverse unconstrained u')
            in
                witnessF . packed . fmap fromFieldElement $ func x u

        func' :: forall ctx' . StepFunctionAssumptions a ctx' => ctx' i -> ctx' p -> ctx' i
        func' x' u' =
            let
                x = FieldElement <$> unpacked x'
                u = FieldElement <$> unpacked u'
            in
                packed . fmap fromFieldElement $ func x u

        predicateCircuit :: PredicateCircuit a i p
        predicateCircuit =
            hlmap (U1 :*:) $
            compileWith @a guessOutput (\(i :*: p) U1 -> (U1 :*: U1 :*: U1, i :*: p :*: U1)) func'
    in Predicate {..}
