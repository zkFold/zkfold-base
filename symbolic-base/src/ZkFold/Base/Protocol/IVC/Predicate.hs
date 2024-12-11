{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Protocol.IVC.Predicate where

import           Data.Binary                       (Binary)
import           GHC.Generics                      ((:*:) (..), U1 (..), type (:.:) (..), Par1 (..))
import           Prelude                           hiding (Num (..), drop, head, replicate, take, zipWith)

import           ZkFold.Base.Data.Vector           (Vector, unsafeToVector)
import           ZkFold.Base.Algebra.Basic.Class   (fromConstant)
import           ZkFold.Base.Algebra.Basic.Number  (KnownNat, value)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Data.FieldElement (FieldElement (..))
import           ZkFold.Symbolic.Compiler          (ArithmeticCircuit, compileWith, hlmap, hpmap, guessOutput)
import           ZkFold.Symbolic.Interpreter       (Interpreter(..))
import           ZkFold.Prelude                    (replicate)

type PredicateCircuit i p f = ArithmeticCircuit f (i :*: p) i U1

data Predicate i p f = Predicate
  { predicateEval    :: i f -> p f -> i f
  , predicateCircuit :: PredicateCircuit i p f
  }

type StepFunction nx nu = forall ctx . Symbolic ctx => Vector nx (FieldElement ctx) -> Vector nu (FieldElement ctx) -> Vector nx (FieldElement ctx)

predicate :: forall nx nu f .
    ( KnownNat nx
    , KnownNat nu
    , Arithmetic f
    , Binary f
    ) => StepFunction nx nu -> Predicate (Vector nx) (Vector nu) f
predicate func =
    let
        predicateEval :: Vector nx f -> Vector nu f -> Vector nx f
        predicateEval x u =
            let x' = fromConstant <$> x :: Vector nx (FieldElement (Interpreter f))
                u' = fromConstant <$> u :: Vector nu (FieldElement (Interpreter f))
            in unPar1 . runInterpreter . fromFieldElement <$> func x' u'

        predicateCircuit :: ArithmeticCircuit f (Vector nx :*: Vector nu) (Vector nx) U1
        predicateCircuit =
            hpmap (\(x :*: u) -> Comp1 (Par1 <$> x) :*: Comp1 (Par1 <$> u)) $
            hlmap (\x -> U1 :*: Comp1 (Par1 <$> x)) $
            compileWith @f guessOutput (\(x :*: u) U1 ->
                    ( Comp1 (unsafeToVector $ replicate (value @nx) U1) :*: Comp1 (unsafeToVector $ replicate (value @nx) U1) :*: U1
                    , x :*: u :*: U1)
                ) func
    in Predicate {..}
