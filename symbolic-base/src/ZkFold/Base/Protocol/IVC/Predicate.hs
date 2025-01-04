{-# LANGUAGE TypeOperators #-}

module ZkFold.Base.Protocol.IVC.Predicate where

import           Data.Binary                           (Binary)
import           GHC.Generics                          (U1 (..), (:*:) (..))
import           Prelude                               hiding (Num (..), drop, head, replicate, take, zipWith)

import           ZkFold.Base.Data.Package              (packed, unpacked)
import           ZkFold.Base.Protocol.IVC.StepFunction (FunctorAssumptions, StepFunction)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler              (ArithmeticCircuit, compileWith, guessOutput, hlmap)
import           ZkFold.Symbolic.Data.FieldElement     (FieldElement (..))
import           ZkFold.Symbolic.Interpreter           (Interpreter(..))

type PredicateEval i p ctx    = i (BaseField ctx) -> p (BaseField ctx) -> i (BaseField ctx)
type PredicateWitness i p ctx = i (WitnessField ctx) -> p (WitnessField ctx) -> i (WitnessField ctx)
type PredicateCircuit i p ctx = ArithmeticCircuit (BaseField ctx) (i :*: p) i U1

data Predicate i p ctx = Predicate
    { predicateEval    :: PredicateEval i p ctx
    , predicateWitness :: PredicateWitness i p ctx
    , predicateCircuit :: PredicateCircuit i p ctx
    }

type PredicateAssumptions a i p =
    ( Arithmetic a
    , Binary a
    , FunctorAssumptions i
    , FunctorAssumptions p
    )

predicate :: forall i p ctx . (PredicateAssumptions (BaseField ctx) i p, Symbolic ctx)
    => StepFunction i p -> Predicate i p ctx
predicate func =
    let
        predicateEval :: i (BaseField ctx) -> p (BaseField ctx) -> i (BaseField ctx)
        predicateEval x u = runInterpreter $ func' (Interpreter x) (Interpreter u)

        predicateWitness :: i (WitnessField ctx) -> p (WitnessField ctx) -> i (WitnessField ctx)
        predicateWitness x' u' =
            let
                x :: i (FieldElement ctx)
                x = fmap FieldElement $ unpacked $ embedW x'

                u :: p (FieldElement ctx)
                u = fmap FieldElement $ unpacked $ embedW u'
            in
                witnessF . packed . fmap fromFieldElement $ func x u

        func' :: forall ctx' . Symbolic ctx' => ctx' i -> ctx' p -> ctx' i
        func' x' u' =
            let
                x = FieldElement <$> unpacked x'
                u = FieldElement <$> unpacked u'
            in
                packed . fmap fromFieldElement $ func x u

        predicateCircuit :: PredicateCircuit i p ctx
        predicateCircuit =
            hlmap (U1 :*:) $
            compileWith @(BaseField ctx) guessOutput (\(i :*: p) U1 -> (U1 :*: U1 :*: U1, i :*: p :*: U1)) func'
    in Predicate {..}
