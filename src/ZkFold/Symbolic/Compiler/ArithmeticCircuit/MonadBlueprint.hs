{-# LANGUAGE DerivingStrategies #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint (
    Eval,
    NewConstraint,
    ClosedPoly,
    MonadBlueprint (..)
) where

import           Control.Monad.State                                    (State, modify)
import           Data.Functor                                           (($>))
import           Data.Map                                               (singleton, (!))
import           Prelude                                                hiding ((*), (-))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate           (monomial, polynomial)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (mappendC)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal    hiding (Constraint, constraint)
import qualified ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal    as I

newtype Self a = Self { getSelf :: a }
    deriving newtype (AdditiveSemigroup, AdditiveMonoid, AdditiveGroup, MultiplicativeSemigroup, MultiplicativeMonoid)

instance Ring a => Scale (Self a) a where
    scale a (Self b) = Self (a * b)

type Eval i a = (i -> a) -> a

type NewConstraint i a = forall x . Algebra x a => (i -> x) -> i -> x

type ClosedPoly i a = forall x . Algebra x a => Eval i x

class (Ring a, Monad m) => MonadBlueprint i a m | m -> i, m -> a where
    runCircuit :: ArithmeticCircuit a -> m i

    newSourced :: [i] -> NewConstraint i a -> Eval i a -> m i

    constraint :: ClosedPoly i a -> m ()

    newConstrained :: NewConstraint i a -> Eval i a -> m i
    newConstrained = newSourced []

    newAssigned :: ClosedPoly i a -> m i
    newAssigned p = newConstrained (\x i -> p x - x i) (\c -> getSelf (p (Self . c)))

instance Arithmetic a => MonadBlueprint Integer a (State (ArithmeticCircuit a)) where
    runCircuit r = modify (mappendC r) $> acOutput r

    newSourced s c e = do
        i <- newVariableWithSource s (c var)
        addVariable i
        constraint (`c` i)
        assignment (\m -> e (m !))
        return i

    constraint p = I.constraint (p var)

var :: Arithmetic a => Integer -> I.Constraint a
var x = polynomial [ monomial one (singleton x one) ]
