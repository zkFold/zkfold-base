{-# LANGUAGE DerivingStrategies #-}

{-# OPTIONS_GHC -Wno-orphans    #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint (
    NewConstraint,
    ClosedPoly,
    MonadBlueprint (..),
    Witness,
    WitnessField,
    circuit,
    circuits
) where

import           Control.Monad.State                                    (State, gets, modify, runState)
import           Data.Functor                                           (($>))
import           Data.Map                                               (singleton, (!))
import           Prelude                                                hiding (Bool (..), Eq (..), (*), (-))
import qualified Prelude                                                as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Scale                        (Self (..))
import           ZkFold.Base.Algebra.Polynomials.Multivariate           (monomial, polynomial)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal    hiding (Constraint, constraint)
import qualified ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal    as I
import           ZkFold.Symbolic.Data.Bool                              (Bool (..), BoolType (..))
import           ZkFold.Symbolic.Data.Conditional                       (Conditional (..))
import           ZkFold.Symbolic.Data.Eq                                (Eq (..))

type WitnessField x a = (Algebra x a, FiniteField x, BinaryExpansion x,
    Eq (Bool x) x, Conditional (Bool x) x, Conditional (Bool x) (Bool x))

type Witness i a = forall x . WitnessField x a => (i -> x) -> x

type NewConstraint i a = forall x . Algebra x a => (i -> x) -> i -> x

type ClosedPoly i a = forall x . Algebra x a => (i -> x) -> x

class (Ring a, Monad m) => MonadBlueprint i a m | m -> i, m -> a where
    input :: m i

    output :: i -> m (ArithmeticCircuit a)

    runCircuit :: ArithmeticCircuit a -> m i

    newSourced :: [i] -> NewConstraint i a -> Witness i a -> m i

    constraint :: ClosedPoly i a -> m ()

    newConstrained :: NewConstraint i a -> Witness i a -> m i
    newConstrained = newSourced []

    newAssigned :: ClosedPoly i a -> m i
    newAssigned p = newConstrained (\x i -> p x - x i) p

instance Arithmetic a => MonadBlueprint Integer a (State (ArithmeticCircuit a)) where
    input = acOutput <$> I.input

    output i = gets (\r -> r { acOutput = i })

    runCircuit r = modify (<> r) $> acOutput r

    newSourced s c e = do
        i <- newVariableWithSource s (c var)
        addVariable i
        constraint (`c` i)
        assignment (\m -> getSelf $ e (Self . (m !)))
        return i

    constraint p = I.constraint (p var)

instance (FiniteField a, Haskell.Eq a) => Eq (Bool (Self a)) (Self a) where
    Self x == Self y = Bool . Self $ bool zero one (x Haskell.== y)
    Self x /= Self y = Bool . Self $ bool zero one (x Haskell./= y)

instance (FiniteField a, Haskell.Eq a) => Conditional (Bool (Self a)) (Self a) where
    bool x y b = if b Haskell.== true then y else x

instance (FiniteField a, Haskell.Eq a) => Conditional (Bool (Self a)) (Bool (Self a)) where
    bool x y b = if b Haskell.== true then y else x

var :: Arithmetic a => Integer -> I.Constraint a
var x = polynomial [(one, monomial (singleton x one))]

circuit :: Arithmetic a => (forall i m . MonadBlueprint i a m => m i) -> ArithmeticCircuit a
circuit b = let (o, r) = runState b mempty in r { acOutput = o }

circuits :: Arithmetic a => (forall i m . MonadBlueprint i a m => m [i]) -> [ArithmeticCircuit a]
circuits b = let (os, r) = runState b mempty in [ r { acOutput = o } | o <- os ]
