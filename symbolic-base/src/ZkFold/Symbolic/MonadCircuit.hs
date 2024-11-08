{-# LANGUAGE DerivingVia   #-}
{-# LANGUAGE TypeOperators #-}

module ZkFold.Symbolic.MonadCircuit where

import           Control.Applicative             (Applicative)
import           Control.Monad                   (Monad (return))
import           Data.Eq                         (Eq)
import           Data.Function                   ((.))
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
-- Witness builders should support all the operations of witnesses,
-- and in addition there should be a corresponding builder for each variable.
class ( FromConstant a w, Scale a w, FiniteField w
      , ToConstant w, FromConstant (Const w) w, SemiEuclidean (Const w)
      ) => Witness i a w | w -> i, w -> a where
  -- | @at x@ is a witness builder whose value is equal to the value of @x@.
  at :: i -> w

-- | A type of polynomial expressions.
-- @var@ is a type of variables, @a@ is a base field.
--
-- A function is a polynomial expression if, given an arbitrary algebra @x@ over
-- @a@ and a function mapping known variables to their witnesses, it computes a
-- new value in that algebra.
--
-- NOTE: the property above is correct by construction for each function of a
-- suitable type, you don't have to check it yourself.
type ClosedPoly var a = forall x . Algebra a x => (var -> x) -> x

-- | A type of constraints for new variables.
-- @var@ is a type of variables, @a@ is a base field.
--
-- A function is a constraint for a new variable if, given an arbitrary algebra
-- @x@ over @a@, a function mapping known variables to their witnesses in that
-- algebra and a new variable, it computes the value of a constraint polynomial
-- in that algebra.
--
-- NOTE: the property above is correct by construction for each function of a
-- suitable type, you don't have to check it yourself.
type NewConstraint var a = forall x . Algebra a x => (var -> x) -> var -> x

-- | A monadic DSL for constructing arithmetic circuits.
-- @var@ is a type of variables, @a@ is a base field, @w@ is a type of witnesses
-- and @m@ is a monad for constructing the circuit.
--
-- DSL provides the following guarantees:
--
-- * Constraints never reference undefined variables;
-- * Variables with equal witnesses are reused as much as possible;
-- * Variables with different witnesses are different;
-- * There is an order in which witnesses can be generated.
--
-- However, DSL does NOT provide the following guarantees (yet):
--
-- * That provided witnesses satisfy the provided constraints. To check this,
--   you can use 'ZkFold.Symbolic.Compiler.ArithmeticCircuit.checkCircuit'.
-- * That introduced constraints are supported by the zk-SNARK utilized for later proving.
class (Monad m, FromConstant a var, Witness var a w) => MonadCircuit var a w m | m -> var, m -> a, m -> w where
  -- | Creates new variable from witness.
  --
  -- NOTE: this does not add any constraints to the system,
  -- use 'rangeConstraint' or 'constraint' to add them.
  unconstrained :: w -> m var

  -- | Adds new polynomial constraint to the system.
  -- E.g., @'constraint' (\\x -> x i)@ forces variable @var@ to be zero.
  --
  -- NOTE: it is not checked (yet) whether provided constraint is in
  -- appropriate form for zkSNARK in use.
  constraint :: ClosedPoly var a -> m ()

  -- | Adds new range constraint to the system.
  -- E.g., @'rangeConstraint' var B@ forces variable @var@ to be in range \([0; B]\).
  rangeConstraint :: var -> a -> m ()

  -- | Creates new variable given a polynomial witness
  -- AND adds a corresponding polynomial constraint.
  --
  -- E.g., @'newAssigned' (\\x -> x i + x j)@ creates new variable @k@
  -- whose value is equal to \(x_i + x_j\)
  -- and a constraint \(x_i + x_j - x_k = 0\).
  --
  -- NOTE: this adds a polynomial constraint to the system.
  --
  -- NOTE: is is not checked (yet) whether the corresponding constraint is in
  -- appropriate form for zkSNARK in use.
  newAssigned :: ClosedPoly var a -> m var
  newAssigned p = newConstrained (\x var -> p x - x var) (p at)

-- | Creates new variable from witness constrained with an inclusive upper bound.
-- E.g., @'newRanged' b (\\x -> x var - one)@ creates new variable whose value
-- is equal to @x var - one@ and which is expected to be in range @[0..b]@.
--
-- NOTE: this adds a range constraint to the system.
newRanged :: MonadCircuit var a w m => a -> w -> m var
newRanged upperBound witness = do
  v <- unconstrained witness
  rangeConstraint v upperBound
  return v

-- | Creates new variable from witness constrained by a polynomial.
-- E.g., @'newConstrained' (\\x i -> x i * (x i - one)) (\\x -> x j - one)@
-- creates new variable whose value is equal to @x j - one@ and which is
-- expected to be a root of the polynomial @x i * (x i - one)@.
--
-- NOTE: this adds a polynomial constraint to the system.
--
-- NOTE: it is not checked (yet) whether provided constraint is in
-- appropriate form for zkSNARK in use.
newConstrained :: MonadCircuit var a w m => NewConstraint var a -> w -> m var
newConstrained poly witness = do
  v <- unconstrained witness
  constraint (`poly` v)
  return v

-- | Field of witnesses with decidable equality and ordering
-- is called an ``arithmetic'' field.
type Arithmetic a = (WitnessField Natural a, Eq a, Ord a)

-- | An example implementation of a @'MonadCircuit'@ which computes witnesses
-- immediately and drops the constraints.
newtype Witnesses n a x = Witnesses { runWitnesses :: x }
  deriving (Functor, Applicative, Monad) via Identity

newtype WitnessOf n a = WitnessOf { witnessOf :: a }
  deriving newtype ( AdditiveSemigroup, AdditiveMonoid, AdditiveGroup, MultiplicativeSemigroup, MultiplicativeMonoid, Field)

deriving newtype instance FromConstant c a => FromConstant c (WitnessOf n a)
instance {-# OVERLAPPING #-} FromConstant (WitnessOf n a) (WitnessOf n a)
deriving newtype instance (ToConstant a, Const a ~ n) => ToConstant (WitnessOf n a)
deriving newtype instance Finite a => Finite (WitnessOf n a)
deriving newtype instance Scale c a => Scale c (WitnessOf n a)
instance {-# OVERLAPPING #-} MultiplicativeSemigroup a => Scale (WitnessOf n a) (WitnessOf n a)
instance Exponent a p => Exponent (WitnessOf n a) p where WitnessOf x ^ p = WitnessOf (x ^ p)
deriving newtype instance Semiring a => Semiring (WitnessOf n a)
deriving newtype instance Ring a => Ring (WitnessOf n a)

instance WitnessField n a => Witness a a (WitnessOf n a) where
  at = WitnessOf

instance WitnessField n a => MonadCircuit a a (WitnessOf n a) (Witnesses n a) where
  unconstrained = return . witnessOf
  constraint _ = return ()
  rangeConstraint _ _ = return ()
