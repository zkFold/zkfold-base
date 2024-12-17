{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.IVC.Predicate where

import           Data.Binary                           (Binary)
import           GHC.Generics                          ((:*:) (..), U1 (..))
import           Prelude                               hiding (Num (..), drop, head, replicate, take, zipWith)

import           ZkFold.Base.Data.Package              (packed, unpacked)
import           ZkFold.Base.Protocol.IVC.StepFunction (FunctorAssumptions, StepFunctionAssumptions, StepFunction)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.FieldElement     (FieldElement (..))
import           ZkFold.Symbolic.Compiler              (ArithmeticCircuit, compileWith, hlmap, guessOutput)
import           ZkFold.Symbolic.Interpreter           (Interpreter(..))

type PredicateCircuit a i p = ArithmeticCircuit a (i :*: p) i U1

data Predicate a i p = Predicate
    { predicateEval    :: i a -> p a -> i a
    , predicateCircuit :: PredicateCircuit a i p
    }

type PredicateAssumptions a i p =
    ( Arithmetic a
    , Binary a
    , FunctorAssumptions i
    , FunctorAssumptions p
    )

predicate :: forall a i p ctx0 ctx1 .
    ( PredicateAssumptions a i p
    , ctx0 ~ Interpreter a
    , StepFunctionAssumptions a (FieldElement ctx0) ctx0
    , ctx1 ~ ArithmeticCircuit a (i :*: p) U1
    , StepFunctionAssumptions a (FieldElement ctx1) ctx1
    ) => StepFunction a i p -> Predicate a i p
predicate func =
    let
        func' :: forall f ctx . StepFunctionAssumptions a f ctx => ctx i -> ctx p -> ctx i
        func' x' u' =
            let
                x = FieldElement <$> unpacked x'
                u = FieldElement <$> unpacked u'
            in
                packed . fmap fromFieldElement $ func x u

        predicateEval :: i a -> p a -> i a
        predicateEval x u = runInterpreter $ func' (Interpreter x) (Interpreter u)

        predicateCircuit :: PredicateCircuit a i p
        predicateCircuit =
            hlmap (U1 :*:) $
            compileWith @a guessOutput (\(i :*: p) U1 -> (U1 :*: U1 :*: U1, i :*: p :*: U1)) func'
    in Predicate {..}
