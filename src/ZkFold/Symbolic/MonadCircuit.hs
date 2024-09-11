{-# LANGUAGE DerivingVia   #-}
{-# LANGUAGE TypeOperators #-}

module ZkFold.Symbolic.MonadCircuit where

import           Control.Applicative             (Applicative)
import           Control.Monad                   (Monad (return))
import           Data.Eq                         (Eq)
import           Data.Function                   (id)
import           Data.Functor                    (Functor)
import           Data.Functor.Identity           (Identity (..))
import           Data.Ord                        (Ord)
import           Data.Type.Equality              (type (~))
import           Numeric.Natural                 (Natural)

import           ZkFold.Base.Algebra.Basic.Class

-- | A @'WitnessField'@ should support all algebraic operations
-- used inside an arithmetic circuit.
type WitnessField n a = ( FiniteField a, ToConstant a, Const a ~ n
                        , FromConstant n a, SemiEuclidean n)

-- | A type of witness builders. @i@ is a type of variables, @a@ is a base field.
--
-- A function is a witness builder if, given an arbitrary field of witnesses @x@
-- over @a@ and a function mapping known variables to their witnesses,
-- it computes the new witness in @x@.
--
-- NOTE: the property above is correct by construction for each function of a
-- suitable type, you don't have to check it yourself.
type Witness i a = forall x n . (Algebra a x, WitnessField n x) => (i -> x) -> x

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

-- | A type of polynomial expressions.
-- @i@ is a type of variables, @a@ is a base field.
--
-- A function is a polynomial expression if, given an arbitrary algebra @x@ over
-- @a@ and a function mapping known variables to their witnesses, it computes a
-- new value in that algebra.
--
-- NOTE: the property above is correct by construction for each function of a
-- suitable type, you don't have to check it yourself.
type ClosedPoly i a = forall x . Algebra a x => (i -> x) -> x

-- | A monadic DSL for constructing arithmetic circuits.
-- @i@ is a type of variables, @a@ is a base field
-- and @m@ is a monad for constructing the circuit.
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
class (Monad m, FromConstant a var) => MonadCircuit var a m | m -> var, m -> a where
    -- | Creates new variable from witness constrained with an inclusive upper bound.
    -- E.g., @'newRanged' b (\\x -> x i - one)@ creates new variable whose value
    -- is equal to @x i - one@ and which is expected to be in range @[0..b]@.
    --
    -- NOTE: this adds a range constraint to the system.
    newRanged :: a -> Witness var a -> m var

    -- | Creates new variable from witness constrained by a polynomial.
    -- E.g., @'newConstrained' (\\x i -> x i * (x i - one)) (\\x -> x j - one)@
    -- creates new variable whose value is equal to @x j - one@ and which is
    -- expected to be a root of the polynomial @x i (x i - one)@.
    --
    -- NOTE: this adds a polynomial contraint to the system.
    --
    -- NOTE: it is not checked (yet) whether provided constraint is in
    -- appropriate form for zkSNARK in use.
    newConstrained :: NewConstraint var a -> Witness var a -> m var

    -- | Adds new polynomial constraint to the system.
    -- E.g., @'constraint' (\\x -> x i)@ forces variable @i@ to be zero.
    --
    -- NOTE: it is not checked (yet) whether provided constraint is in
    -- appropriate form for zkSNARK in use.
    constraint :: ClosedPoly var a -> m ()

    -- | A wrapper around @'newConstrained'@ which creates
    -- new variable given a polynomial witness.
    -- E.g., @'newAssigned' (\\x -> x i + x j)@ creates new variable
    -- whose value is equal to @x i + x j@.
    --
    -- NOTE: this adds a polynomial constraint to the system.
    --
    -- NOTE: is is not checked (yet) whether the corresponding constraint is in
    -- appropriate form for zkSNARK in use.
    newAssigned :: ClosedPoly var a -> m var
    newAssigned p = newConstrained (\x i -> p x - x i) p

-- | Field of witnesses with decidable equality and ordering
-- is called an ``arithmetic'' field.
type Arithmetic a = (WitnessField Natural a, Eq a, Ord a)

-- | An example implementation of a @'MonadCircuit'@ which computes witnesses
-- immediately and drops the constraints.
newtype Witnesses n a x = Witnesses { runWitnesses :: x }
  deriving (Functor, Applicative, Monad) via Identity

instance WitnessField n a => MonadCircuit a a (Witnesses n a) where
    newRanged _ w = return (w id)
    newConstrained _ w = return (w id)
    constraint _ = return ()
    newAssigned w = return (w id)
