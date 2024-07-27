{-# LANGUAGE TypeOperators #-}

module ZkFold.Symbolic.Class where

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

type CircuitFun f g a = forall i m. MonadCircuit i a m => f i -> m (g i)

class (HApplicative c, Package c, SymbolicField (BaseField c)) => Symbolic c where
    type BaseField c :: Type

    symbolicF :: BaseField c ~ a => c f -> (f a -> g a) -> CircuitFun f g a -> c g

    fromCircuitF :: c f -> CircuitFun f g (BaseField c) -> c g
    fromCircuitF x f = symbolicF x (runWitnesses @(BaseField c) . f) f

embed :: (Symbolic c, Foldable f, Functor f) => f (BaseField c) -> c f
embed = packed . fmap (\x ->
    fromCircuitF hunit $ const $ Par1 <$> newAssigned (const $ fromConstant x))

symbolic2F ::
    (Symbolic c, BaseField c ~ a) => c f -> c g -> (f a -> g a -> h a) ->
    (forall i m. MonadCircuit i a m => f i -> g i -> m (h i)) -> c h
symbolic2F x y f m = symbolicF (hpair x y) (uncurryP f) (uncurryP m)

fromCircuit2F :: Symbolic c => c f -> c g -> (forall i m. MonadCircuit i (BaseField c) m => f i -> g i -> m (h i)) -> c h
fromCircuit2F x y m = fromCircuitF (hpair x y) (uncurryP m)

symbolicVF ::
    (Symbolic c, BaseField c ~ a, Foldable f, Functor f) =>
    f (c g) -> (f (g a) -> h a) ->
    (forall i m. MonadCircuit i a m => f (g i) -> m (h i)) -> c h
symbolicVF xs f m = symbolicF (pack xs) (f . unComp1) (m . unComp1)

fromCircuitVF ::
    (Symbolic c, Foldable f, Functor f) => f (c g) ->
    (forall i m. MonadCircuit i (BaseField c) m => f (g i) -> m (h i)) -> c h
fromCircuitVF xs m = fromCircuitF (pack xs) (m . unComp1)
