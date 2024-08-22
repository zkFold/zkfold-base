{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.MonadBlueprint (
    ClosedPoly,
    MonadBlueprint (..),
    NewConstraint,
    Witness,
    WitnessField,
    circuit,
    circuitF,
    circuits
) where

import           Control.Applicative                                 (pure)
import           Control.Monad.State                                 (State, modify, runState)
import           Data.Foldable                                       (Foldable)
import           Data.Functor                                        (Functor, fmap, ($>), (<$>))
import           Data.Functor.Rep                                    (Representable (..))
import           Data.Monoid                                         (mempty, (<>))
import           Data.Ord                                            (Ord)
import           GHC.Generics                                        (Par1, U1 (..))

import           ZkFold.Base.Algebra.Basic.Class                     (ToConstant)
import           ZkFold.Base.Algebra.Basic.Number                    (Natural)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal hiding (constraint)
import           ZkFold.Symbolic.MonadCircuit

-- | A @'MonadCircuit'@ with an added capability
-- of embedding another arithmetic circuit inside.
class MonadCircuit v a m => MonadBlueprint i v a m | m -> i where
    -- | Adds the supplied circuit to the blueprint and returns its output variable.
    runCircuit :: ArithmeticCircuit a i o -> m (o v)

instance (Arithmetic a, Ord (Rep i), Foldable i, Representable i, ToConstant (Rep i) Natural) => MonadBlueprint i (Var i) a (State (ArithmeticCircuit a i U1)) where
    runCircuit r = modify (<> r {acOutput = U1}) $> acOutput r

circuit :: (Arithmetic a, Ord (Rep i), Foldable i, Representable i, ToConstant (Rep i) Natural) => (forall v m . MonadBlueprint i v a m => m v) -> ArithmeticCircuit a i Par1
-- ^ Builds a circuit from blueprint. A blueprint is a function which, given an
-- arbitrary type of variables @i@ and a monad @m@ supporting the 'MonadBlueprint'
-- API, computes the output variable of a future circuit.
circuit b = circuitF (pure <$> b)

circuitF :: forall a i o . (Arithmetic a, Ord (Rep i), Foldable i, Representable i, ToConstant (Rep i) Natural) => (forall v m . MonadBlueprint i v a m => m (o v)) -> ArithmeticCircuit a i o
-- TODO: I should really rethink this...
circuitF b = let (os, r) = runState b mempty
              in r { acOutput = os }

-- TODO: kept for compatibility with @binaryExpansion@ only. Perhaps remove it in the future?
circuits :: forall a i o . (Arithmetic a, Functor o, Ord (Rep i), Foldable i, Representable i, ToConstant (Rep i) Natural) => (forall v m . MonadBlueprint i v a m => m (o v)) -> o (ArithmeticCircuit a i Par1)
-- ^ Builds a collection of circuits from one blueprint. A blueprint is a function
-- which, given an arbitrary type of variables @i@ and a monad @m@ supporting the
-- 'MonadBlueprint' API, computes the collection of output variables of future circuits.
circuits b = let (os, r) = runState (fmap pure <$> b) mempty in (\o -> r { acOutput = o }) <$> os
