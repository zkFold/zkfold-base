{-# LANGUAGE TypeOperators #-}

module ZkFold.Base.Protocol.IVC.Predicate where

import           Control.DeepSeq                       (NFData)
import           Data.Binary                           (Binary)
import           Data.Functor.Rep                      (Representable (..))
import           GHC.Generics                          (U1 (..), (:*:) (..))
import           Prelude                               hiding (Num (..), drop, head, replicate, take, zipWith)

import           ZkFold.Base.Data.Package              (packed, unpacked)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler              (ArithmeticCircuit, compileWith, guessOutput, hlmap)
import           ZkFold.Symbolic.Data.FieldElement     (FieldElement (..))

type StepFunction i p = forall ctx . Symbolic ctx => i (FieldElement ctx) -> p (FieldElement ctx) -> i (FieldElement ctx)

type PredicateWitness i p ctx = i (WitnessField ctx) -> p (WitnessField ctx) -> i (WitnessField ctx)
type PredicateCircuit i p ctx = ArithmeticCircuit (BaseField ctx) (i :*: p) i i

data Predicate i p ctx = Predicate
    { predicateWitness :: PredicateWitness i p ctx
    , predicateCircuit :: PredicateCircuit i p ctx
    }

type FunctorAssumptions f =
    ( Representable f
    , Traversable f
    , NFData (Rep f)
    , Binary (Rep f)
    , Ord (Rep f)
    )

predicate :: forall i p ctx .
    ( Symbolic ctx
    , Binary (BaseField ctx)
    , FunctorAssumptions i
    , FunctorAssumptions p
    ) => StepFunction i p -> Predicate i p ctx
predicate func =
    let
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
