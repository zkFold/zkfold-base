{-# LANGUAGE TypeOperators #-}

module ZkFold.Symbolic.Class
  ( Symbolic (..)
  , Arithmetic
  , embed
  , symbolic2F
  , fromCircuit2F
  , symbolic3F
  , fromCircuit3F
  , symbolicVF
  , fromCircuitVF
  ) where

import           Data.Foldable                    (Foldable)
import           Data.Function                    (const, ($), (.))
import           Data.Functor                     (Functor (fmap), (<$>))
import           Data.Kind                        (Type)
import           Data.Type.Equality               (type (~))
import           GHC.Generics                     (Par1 (Par1), type (:.:) (unComp1))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Control.HApplicative (HApplicative (hpair, hunit))
import           ZkFold.Base.Data.Package         (Package (pack), packed)
import           ZkFold.Base.Data.Product         (uncurryP)
import           ZkFold.Symbolic.MonadCircuit

-- | A type of mappings between functors inside a circuit.
-- @f@ is an input functor, @g@ is an output functor, @a@ is a base field.
--
-- A function is a mapping between functors inside a circuit if,
-- given an arbitrary builder of circuits @m@ over @a@ with arbitrary @i@ as
-- variables, it maps @f@ many inputs to @g@ many outputs using @m@.
--
-- NOTE: the property above is correct by construction for each function of a
-- suitable type, you don't have to check it yourself.
type CircuitFun f g a = forall i m. MonadCircuit i a m => f i -> m (g i)

-- | A Symbolic DSL for performant pure computations with arithmetic circuits.
-- @c@ is a generic context in which computations are performed.
class (HApplicative c, Package c, Arithmetic (BaseField c)) => Symbolic c where
    -- | Base algebraic field over which computations are performed.
    type BaseField c :: Type

    -- | To perform computations in a generic context @c@ -- that is,
    -- to form a mapping between @c f@ and @c g@ for given @f@ and @g@ --
    -- you need to provide two things:
    --
    -- 1. An algorithm for turning @f@ into @g@ in a pure context;
    -- 2. An algorithm for turning @f@ into @g@ inside a circuit.
    --
    -- It is not however checked (yet) that the provided algorithms
    -- compute the same things.
    --
    -- If the pure-context computation is tautological to the circuit
    -- computation, use @'fromCircuitF'@.
    symbolicF :: BaseField c ~ a => c f -> (f a -> g a) -> CircuitFun f g a -> c g

    -- | A wrapper around @'symbolicF'@ which extracts the pure computation
    -- from the circuit computation using the @'Witnesses'@ newtype.
    fromCircuitF :: c f -> CircuitFun f g (BaseField c) -> c g
    fromCircuitF x f = symbolicF x (runWitnesses @(BaseField c) . f) f

-- | Embeds the pure value(s) into generic context @c@.
embed :: (Symbolic c, Foldable f, Functor f) => f (BaseField c) -> c f
embed = packed . fmap (\x ->
    fromCircuitF hunit $ const $ Par1 <$> newAssigned (const $ fromConstant x))

symbolic2F ::
    (Symbolic c, BaseField c ~ a) => c f -> c g -> (f a -> g a -> h a) ->
    (forall i m. MonadCircuit i a m => f i -> g i -> m (h i)) -> c h
-- | Runs the binary function from @f@ and @g@ into @h@ in a generic context @c@.
symbolic2F x y f m = symbolicF (hpair x y) (uncurryP f) (uncurryP m)

fromCircuit2F ::
    Symbolic c => c f -> c g ->
    (forall i m. MonadCircuit i (BaseField c) m => f i -> g i -> m (h i)) -> c h
-- | Runs the binary @'CircuitFun'@ in a generic context.
fromCircuit2F x y m = fromCircuitF (hpair x y) (uncurryP m)

symbolic3F ::
    (Symbolic c, BaseField c ~ a) => c f -> c g -> c h -> (f a -> g a -> h a -> k a) ->
    (forall i m. MonadCircuit i a m => f i -> g i -> h i -> m (k i)) -> c k
-- | Runs the ternary function from @f@, @g@ and @h@ into @k@ in a context @c@.
symbolic3F x y z f m = symbolic2F (hpair x y) z (uncurryP f) (uncurryP m)

fromCircuit3F ::
    Symbolic c => c f -> c g -> c h ->
    (forall i m. MonadCircuit i (BaseField c) m => f i -> g i -> h i -> m (k i)) -> c k
-- | Runs the ternary @'CircuitFun'@ in a generic context.
fromCircuit3F x y z m = fromCircuit2F (hpair x y) z (uncurryP m)

symbolicVF ::
    (Symbolic c, BaseField c ~ a, Foldable f, Functor f) =>
    f (c g) -> (f (g a) -> h a) ->
    (forall i m. MonadCircuit i a m => f (g i) -> m (h i)) -> c h
-- | Given a generic context @c@, runs the function from @f@ many @c g@'s into @c h@.
symbolicVF xs f m = symbolicF (pack xs) (f . unComp1) (m . unComp1)

fromCircuitVF ::
    (Symbolic c, Foldable f, Functor f) => f (c g) ->
    (forall i m. MonadCircuit i (BaseField c) m => f (g i) -> m (h i)) -> c h
-- | Given a generic context @c@, runs the @'CircuitFun'@ from @f@ many @c g@'s into @c h@.
fromCircuitVF xs m = fromCircuitF (pack xs) (m . unComp1)
