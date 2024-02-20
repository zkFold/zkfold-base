{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeApplications   #-}

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
import           Data.Set                                               (Set)
import qualified Data.Set                                               as Set
import           Prelude                                                hiding (Bool (..), Eq (..), replicate, (*), (-))
import qualified Prelude                                                as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Scale                        (Self (..))
import           ZkFold.Base.Algebra.Polynomials.Multivariate           (monomial, polynomial)
import           ZkFold.Prelude                                         (replicate)
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

    newConstrained :: NewConstraint i a -> Witness i a -> m i

    constraint :: ClosedPoly i a -> m ()

    newAssigned :: ClosedPoly i a -> m i
    newAssigned p = newConstrained (\x i -> p x - x i) p

instance Arithmetic a => MonadBlueprint Integer a (State (ArithmeticCircuit a)) where
    input = acOutput <$> I.input

    output i = gets (\r -> r { acOutput = i })

    runCircuit r = modify (<> r) $> acOutput r

    newConstrained c e = do
        let s = sources e `Set.difference` sources (`c` (-1))
        i <- newVariableWithSource (Set.toList s) (c var)
        addVariable i
        constraint (`c` i)
        assignment (\m -> getSelf $ e (Self . (m !)))
        return i

    constraint p = I.constraint (p var)

circuit :: Arithmetic a => (forall i m . MonadBlueprint i a m => m i) -> ArithmeticCircuit a
circuit b = let (o, r) = runState b mempty in r { acOutput = o }

circuits :: Arithmetic a => (forall i m . MonadBlueprint i a m => m [i]) -> [ArithmeticCircuit a]
circuits b = let (os, r) = runState b mempty in [ r { acOutput = o } | o <- os ]

var :: Arithmetic a => Integer -> I.Constraint a
var x = polynomial [(one, monomial (singleton x one))]

instance (FiniteField a, Haskell.Eq a) => Eq (Bool (Self a)) (Self a) where
    Self x == Self y = Bool . Self $ bool zero one (x Haskell.== y)
    Self x /= Self y = Bool . Self $ bool zero one (x Haskell./= y)

instance (FiniteField a, Haskell.Eq a) => Conditional (Bool (Self a)) (Self a) where
    bool x y b = if b Haskell.== true then y else x

instance (FiniteField a, Haskell.Eq a) => Conditional (Bool (Self a)) (Bool (Self a)) where
    bool x y b = if b Haskell.== true then y else x

sources :: forall i a . (FiniteField a, Ord i) => Witness i a -> Set i
sources = runSources . ($ Sources @a . Set.singleton)

newtype Sources a i = Sources { runSources :: Set i } deriving newtype (Semigroup, Monoid)

instance Ord i => AdditiveSemigroup (Sources a i) where
  (+) = (<>)

instance Ord i => AdditiveMonoid (Sources a i) where
  zero = mempty

instance Ord i => AdditiveGroup (Sources a i) where
  negate = id

instance (Semiring a, Ord i) => Scale (Sources a i) a where
  scale = const id

instance Finite a => Finite (Sources a i) where
  order = order @a

instance Ord i => MultiplicativeSemigroup (Sources a i) where
  (*) = (<>)

instance Ord i => MultiplicativeMonoid (Sources a i) where
  one = mempty

instance Ord i => MultiplicativeGroup (Sources a i) where
  invert = id

instance (Finite a, Ord i) => BinaryExpansion (Sources a i) where
  binaryExpansion = replicate (numberOfBits @a)

instance (Finite a, Ord i) => Eq (Bool (Sources a i)) (Sources a i) where
  x == y = Bool (x <> y)
  x /= y = Bool (x <> y)

instance (Finite a, Ord i) => Conditional (Bool (Sources a i)) (Sources a i) where
  bool x y (Bool b) = x <> y <> b

instance (Finite a, Ord i) => Conditional (Bool (Sources a i)) (Bool (Sources a i)) where
  bool (Bool x) (Bool y) (Bool b) = Bool (x <> y <> b)
