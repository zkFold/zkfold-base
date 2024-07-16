{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeOperators      #-}

{-# OPTIONS_GHC -Wno-orphans    #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint (
    ClosedPoly,
    MonadBlueprint (..),
    NewConstraint,
    Witness,
    WitnessField,
    circuit,
    circuitN,
    circuits
) where

import           Control.Applicative                                 (pure)
import           Control.Monad                                       (Monad, return, (=<<))
import           Control.Monad.State                                 (State, modify, runState)
import           Data.Foldable                                       (maximum)
import           Data.Function                                       (($), (.))
import           Data.Functor                                        (Functor, fmap, ($>), (<$>))
import           Data.Map                                            ((!))
import           Data.Monoid                                         (mempty, (<>))
import           Data.Ord                                            (Ord)
import           Data.Set                                            (Set)
import qualified Data.Set                                            as Set
import           Data.Type.Equality                                  (type (~))
import           Numeric.Natural                                     (Natural)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Sources
import           ZkFold.Base.Algebra.Polynomials.Multivariate        (var)
import           ZkFold.Base.Data.Vector
import qualified ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal as I
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal hiding (constraint)

type WitnessField a x = (Algebra a x, FiniteField x, BinaryExpansion x, Bits x ~ [x])
-- ^ DSL for constructing witnesses in an arithmetic circuit. @a@ is a base
-- field; @x@ is a "field of witnesses over @a@" which you can safely assume to
-- be identical to @a@ with internalized equality.

type Witness i a = forall x . WitnessField a x => (i -> x) -> x
-- ^ A type of witness builders. @i@ is a type of variables, @a@ is a base field.
--
-- A function is a witness builer if, given an arbitrary field of witnesses @x@
-- over @a@ and a function mapping known variables to their witnesses, it computes
-- the new witness in @x@.
--
-- NOTE: the property above is correct by construction for each function of a
-- suitable type, you don't have to check it yourself.

type NewConstraint i a = forall x . Algebra a x => (i -> x) -> i -> x
-- ^ A type of constraints for new variables. @i@ is a type of variables, @a@ is a base field.
--
-- A function is a constraint for a new variable if, given an arbitrary algebra
-- @x@ over @a@, a function mapping known variables to their witnesses in that
-- algebra and a new variable, it computes the value of a constraint polynomial
-- in that algebra.
--
-- NOTE: the property above is correct by construction for each function of a
-- suitable type, you don't have to check it yourself.

type ClosedPoly i a = forall x . Algebra a x => (i -> x) -> x
-- ^ A type of polynomial expressions. @i@ is a type of variables, @a@ is a base field.
--
-- A function is a polynomial expression if, given an arbitrary algebra @x@ over
-- @a@ and a function mapping known variables to their witnesses, it computes a
-- new value in that algebra.
--
-- NOTE: the property above is correct by construction for each function of a
-- suitable type, you don't have to check it yourself.

class Monad m => MonadBlueprint i a m | m -> i, m -> a where
    -- ^ DSL for constructing arithmetic circuits. @i@ is a type of variables,
    -- @a@ is a base field and @m@ is a monad for constructing the circuit.
    --
    -- DSL provides the following guarantees:
    -- * There are no unconstrained variables;
    -- * Variables with equal constraints and witnesses are reused as much as possible;
    -- * Variables with either different constraints or different witnesses are different;
    -- * There is an order in which witnesses can be generated;
    -- * Constraints never reference undefined variables.
    --
    -- However, DSL does NOT provide the following guarantees (yet):
    -- * That provided witnesses satisfy the provided constraints. To check this,
    --   you can use 'ZkFold.Symbolic.Compiler.ArithmeticCircuit.checkCircuit'.
    -- * That introduced polynomial constraints are supported by the zk-SNARK
    --   utilized for later proving.

    -- | Creates new input variable.
    input :: m i

    -- | Adds the supplied circuit to the blueprint and returns its output variable.
    runCircuit :: ArithmeticCircuit a n -> m (Vector n i)

    -- | Creates new variable given an inclusive upper bound on a value and a witness.
    -- e.g., @newRanged b (\\x -> x i - one)@ creates new variable whose value
    -- is equal to @x i - one@ and which is expected to be in range @[0..b]@.
    newRanged :: a -> Witness i a -> m i

    -- | Creates new variable given a constraint polynomial and a witness.
    newConstrained :: NewConstraint i a -> Witness i a -> m i

    -- | Adds new constraint to the system.
    constraint :: ClosedPoly i a -> m ()

    -- | Creates new variable given a polynomial witness.
    newAssigned :: ClosedPoly i a -> m i
    newAssigned p = newConstrained (\x i -> p x - x i) p

instance Arithmetic a => MonadBlueprint Natural a (State (Circuit a)) where
    input = I.input

    runCircuit r = modify (<> acCircuit r) $> acOutput r

    newRanged upperBound witness = do
        let s   = sources @a witness
            -- | A wild (and obviously incorrect) approximation of
            -- x (x - 1) ... (x - upperBound)
            -- It's ok because we only use it for variable generation anyway.
            p i = var i * (var i - fromConstant upperBound)
        i <- addVariable =<< newVariableWithSource (Set.toList s) p
        I.rangeConstraint i upperBound
        assignment i (\m -> witness (m !))
        return i

    newConstrained
        :: NewConstraint Natural a
        -> Witness Natural a
        -> State (Circuit a) Natural
    newConstrained new witness = do
        let ws = sources @a witness
            -- | We need a throwaway variable to feed into `new` which definitely would not be present in a witness
            x = maximum (Set.mapMonotonic (+1) ws <> Set.singleton 0)
            -- | `s` is meant to be a set of variables used in a witness not present in a constraint.
            s = ws `Set.difference` sources @a (`new` x)
        i <- addVariable =<< newVariableWithSource (Set.toList s) (new var)
        constraint (`new` i)
        assignment i (\m -> witness (m !))
        return i

    constraint p = I.constraint (p var)

circuit :: Arithmetic a => (forall i m . MonadBlueprint i a m => m i) -> ArithmeticCircuit a 1
-- ^ Builds a circuit from blueprint. A blueprint is a function which, given an
-- arbitrary type of variables @i@ and a monad @m@ supporting the 'MonadBlueprint'
-- API, computes the output variable of a future circuit.
circuit b = circuitN (pure <$> b)

circuitN :: forall a n . Arithmetic a => (forall i m . MonadBlueprint i a m => m (Vector n i)) -> ArithmeticCircuit a n
-- TODO: I should really rethink this...
circuitN b = let (os, r) = runState b (mempty :: Circuit a)
              in ArithmeticCircuit { acCircuit = r, acOutput = os }

-- TODO: kept for compatibility with @binaryExpansion@ only. Perhaps remove it in the future?
circuits :: forall a f . (Arithmetic a, Functor f) => (forall i m . MonadBlueprint i a m => m (f i)) -> f (ArithmeticCircuit a 1)
-- ^ Builds a collection of circuits from one blueprint. A blueprint is a function
-- which, given an arbitrary type of variables @i@ and a monad @m@ supporting the
-- 'MonadBlueprint' API, computes the collection of output variables of future circuits.
circuits b = let (os, r) = runState (fmap pure <$> b) (mempty :: Circuit a) in (\o -> ArithmeticCircuit { acCircuit = r, acOutput = o }) <$> os

sources :: forall a i . (FiniteField a, Ord i) => Witness i a -> Set i
sources = runSources . ($ Sources @a . Set.singleton)
