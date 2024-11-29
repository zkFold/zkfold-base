{-# LANGUAGE AllowAmbiguousTypes #-}
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

data Predicate a i p = Predicate
  { predicateEval    :: i a -> p a -> i a
  , predicateCircuit :: ArithmeticCircuit a (i :*: p) i U1
  }

type StepFunction nx nu = forall ctx . Symbolic ctx => Vector nx (FieldElement ctx) -> Vector nu (FieldElement ctx) -> Vector nx (FieldElement ctx)

predicate :: forall a nx nu .
    ( Arithmetic a
    , Binary a
    , KnownNat nx
    , KnownNat nu
    ) => StepFunction nx nu -> Predicate a (Vector nx) (Vector nu)
predicate func =
    let
        predicateEval :: Vector nx a -> Vector nu a -> Vector nx a
        predicateEval x u =
            let x' = fromConstant <$> x :: Vector nx (FieldElement (Interpreter a))
                u' = fromConstant <$> u :: Vector nu (FieldElement (Interpreter a))
            in unPar1 . runInterpreter . fromFieldElement <$> func x' u'

        predicateCircuit :: ArithmeticCircuit a (Vector nx :*: Vector nu) (Vector nx) U1
        predicateCircuit =
            hpmap (\(x :*: u) -> Comp1 (Par1 <$> x) :*: Comp1 (Par1 <$> u)) $
            hlmap (\x -> U1 :*: Comp1 (Par1 <$> x)) $
            compileWith @a guessOutput (\(x :*: u) U1 ->
                    ( Comp1 (unsafeToVector $ replicate (value @nx) U1) :*: Comp1 (unsafeToVector $ replicate (value @nx) U1) :*: U1
                    , x :*: u :*: U1)
                ) func
    in Predicate {..}