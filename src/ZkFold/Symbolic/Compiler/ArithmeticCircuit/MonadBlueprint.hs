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
import           Data.Functor                                        (Functor, fmap, ($>), (<$>))
import           Data.Monoid                                         (mempty, (<>))
import           GHC.Generics                                        (Par1)
import           Numeric.Natural                                     (Natural)

import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal hiding (constraint)
import           ZkFold.Symbolic.MonadCircuit

class MonadCircuit i a m => MonadBlueprint i a m where
    -- ^ A @'MonadCircuit'@ with an added capability
    -- of embedding another arithmetic circuit inside.

    -- | Adds the supplied circuit to the blueprint and returns its output variable.
    runCircuit :: ArithmeticCircuit a f -> m (f i)

instance Arithmetic a => MonadBlueprint Natural a (State (Circuit a)) where
    runCircuit r = modify (<> acCircuit r) $> acOutput r

circuit :: Arithmetic a => (forall i m . MonadBlueprint i a m => m i) -> ArithmeticCircuit a Par1
-- ^ Builds a circuit from blueprint. A blueprint is a function which, given an
-- arbitrary type of variables @i@ and a monad @m@ supporting the 'MonadBlueprint'
-- API, computes the output variable of a future circuit.
circuit b = circuitF (pure <$> b)

circuitF :: forall a f . Arithmetic a => (forall i m . MonadBlueprint i a m => m (f i)) -> ArithmeticCircuit a f
-- TODO: I should really rethink this...
circuitF b = let (os, r) = runState b (mempty :: Circuit a)
              in ArithmeticCircuit { acCircuit = r, acOutput = os }

-- TODO: kept for compatibility with @binaryExpansion@ only. Perhaps remove it in the future?
circuits :: forall a f . (Arithmetic a, Functor f) => (forall i m . MonadBlueprint i a m => m (f i)) -> f (ArithmeticCircuit a Par1)
-- ^ Builds a collection of circuits from one blueprint. A blueprint is a function
-- which, given an arbitrary type of variables @i@ and a monad @m@ supporting the
-- 'MonadBlueprint' API, computes the collection of output variables of future circuits.
circuits b = let (os, r) = runState (fmap pure <$> b) (mempty :: Circuit a) in (\o -> ArithmeticCircuit { acCircuit = r, acOutput = o }) <$> os
