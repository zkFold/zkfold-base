{-# LANGUAGE DerivingVia   #-}
{-# LANGUAGE TypeOperators #-}

module ZkFold.Symbolic.MonadCircuit where

import           Control.Applicative             (Applicative)
import           Control.Monad                   (Monad (return))
import           Data.Function                   (id)
import           Data.Functor                    (Functor)
import           Data.Functor.Identity           (Identity (..))
import           Data.Type.Equality              (type (~))

import           ZkFold.Base.Algebra.Basic.Class

-- | A @'WitnessField'@ should support all algebraic operations
-- used inside an arithmetic circuit.
type WitnessField a = (FiniteField a, BinaryExpansion a, Bits a ~ [a])

-- | A type of witness builders. @i@ is a type of variables, @a@ is a base field.
--
-- A function is a witness builder if, given an arbitrary field of witnesses @x@
-- over @a@ and a function mapping known variables to their witnesses,
-- it computes the new witness in @x@.
--
-- NOTE: the property above is correct by construction for each function of a
-- suitable type, you don't have to check it yourself.
type Witness i a = forall x . (Algebra a x, WitnessField x) => (i -> x) -> x

-- | A type of constraints for new variables.
-- @i@ is a type of variables, @a@ is a base field.
--
-- A function is a constraint for a new variable if, given an arbitrary algebra
-- @x@ over @a@, a function mapping known variables to their witnesses in that
-- algebra and a new variable, it computes the value of a constraint polynomial
-- in that algebra.
--
-- NOTE: the property above is correct by construction for each function of a
-- suitable type, you don't have to check it yourself.
type NewConstraint i a = forall x . Algebra a x => (i -> x) -> i -> x

-- | A type of polynomial expressions. @i@ is a type of variables, @a@ is a base field.
--
-- A function is a polynomial expression if, given an arbitrary algebra @x@ over
-- @a@ and a function mapping known variables to their witnesses, it computes a
-- new value in that algebra.
--
-- NOTE: the property above is correct by construction for each function of a
-- suitable type, you don't have to check it yourself.
type ClosedPoly i a = forall x . Algebra a x => (i -> x) -> x

-- | A monadic DSL for constructing arithmetic circuits. @i@ is a type of variables,
-- @a@ is a base field and @m@ is a monad for constructing the circuit.
--
-- DSL provides the following guarantees:
--
-- * There are no unconstrained variables;
-- * Variables with equal constraints and witnesses are reused as much as possible;
-- * Variables with either different constraints or different witnesses are different;
-- * There is an order in which witnesses can be generated;
-- * Constraints never reference undefined variables.
--
-- However, DSL does NOT provide the following guarantees (yet):
--
-- * That provided witnesses satisfy the provided constraints. To check this,
--   you can use 'ZkFold.Symbolic.Compiler.ArithmeticCircuit.checkCircuit'.
-- * That introduced constraints are supported by the zk-SNARK utilized for later proving.
class Monad m => MonadCircuit i a m | m -> i, m -> a where
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

-- | An example implementation of a @'MonadCircuit'@ which computes witnesses
-- immediately and drops the constraints.
newtype Witnesses a x = Witnesses { runWitnesses :: x }
  deriving (Functor, Applicative, Monad) via Identity

instance WitnessField a => MonadCircuit a a (Witnesses a) where
    newRanged _ w = return (w id)
    newConstrained _ w = return (w id)
    constraint _ = return ()
    newAssigned w = return (w id)
