{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.IVC.Predicate where

import           Data.Binary                     (Binary)
import           GHC.Generics                    (U1 (..), (:*:) (..))
import           Prelude                         hiding (Num (..), drop, head, replicate, take, zipWith)

import           ZkFold.Base.Algebra.Basic.Class (FiniteField, FromConstant, Scale)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler        (ArithmeticCircuit, compileWith, guessOutput, hlmap)
import           ZkFold.Symbolic.Data.Class      (LayoutFunctor)

type PredicateFunctionAssumptions a f =
    ( FiniteField f
    , FromConstant a f
    , Scale a f
    )

type PredicateFunction a i p =
  forall c. (Symbolic c, BaseField c ~ a) => c i -> c p -> c i
type PredicateCircuit a i p  = ArithmeticCircuit a (i :*: p) i i

data Predicate a i p = Predicate
    { predicateFunction :: PredicateFunction a i p
    , predicateCircuit  :: PredicateCircuit a i p
    }

predicate :: forall a i p .
    ( Arithmetic a
    , Binary a
    , LayoutFunctor i
    , LayoutFunctor p
    ) => PredicateFunction a i p -> Predicate a i p
predicate predicateFunction =
    let
        predicateCircuit :: PredicateCircuit a i p
        predicateCircuit =
            hlmap (U1 :*:) $
            compileWith @a guessOutput (\(i :*: p) U1 -> (U1 :*: U1 :*: U1, i :*: p :*: U1)) predicateFunction
    in Predicate {..}
