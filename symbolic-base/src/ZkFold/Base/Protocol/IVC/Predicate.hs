{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.IVC.Predicate where

import           Control.DeepSeq                   (NFData)
import           Data.Binary                       (Binary)
import           Data.Functor.Rep                  (Representable (..))
import           GHC.Generics                      ((:*:) (..), U1 (..))
import           Prelude                           hiding (Num (..), drop, head, replicate, take, zipWith)

import           ZkFold.Base.Data.Package          (packed, unpacked)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.FieldElement (FieldElement (..))
import           ZkFold.Symbolic.Compiler          (ArithmeticCircuit, compileWith, hlmap, guessOutput)
import           ZkFold.Symbolic.Interpreter       (Interpreter(..))

type PredicateCircuit a i p = ArithmeticCircuit a (i :*: p) i U1

data Predicate a i p = Predicate
  { predicateEval    :: i a -> p a -> i a
  , predicateCircuit :: PredicateCircuit a i p
  }

type StepFunction a i p = forall ctx . (Symbolic ctx, BaseField ctx ~ a) => i (FieldElement ctx) -> p (FieldElement ctx) -> i (FieldElement ctx)

predicate :: forall a i p .
    ( Representable i
    , Traversable i
    , NFData (Rep i)
    , Binary (Rep i)
    , Ord (Rep i)
    , Representable p
    , Traversable p
    , NFData (Rep p)
    , Binary (Rep p)
    , Ord (Rep p)
    , Arithmetic a
    , Binary a
    ) => StepFunction a i p -> Predicate a i p
predicate func =
    let
        func' :: forall ctx . (Symbolic ctx, BaseField ctx ~ a) => ctx i -> ctx p -> ctx i
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
