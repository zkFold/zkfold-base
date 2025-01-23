{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE TypeOperators         #-}

module ZkFold.Symbolic.Fold where

import           Control.DeepSeq       (NFData, NFData1)
import           Data.Binary           (Binary)
import           Data.Functor.Rep      (Representable (..))
import           Data.List.Infinite    (Infinite)
import           Data.Ord              (Ord)
import           Data.Traversable      (Traversable)
import           Data.Type.Equality    (type (~))
import           GHC.Generics          (Par1)

import           ZkFold.Symbolic.Class (Symbolic (..))

class Symbolic c => SymbolicFold c where
  sfoldl ::
    (Binary (Rep f), NFData (Rep f), Ord (Rep f)) =>
    (forall a. Binary a => Binary (f a)) =>
    (Representable f, NFData1 f, Traversable f) =>
    (Binary (Rep p), Representable p) =>
    (Binary (Rep g), NFData (Rep g), Ord (Rep g), Representable g) =>
    (forall a. Binary a => Binary (h a)) =>
    (WitnessField c ~ wc) =>
    (forall s. (SymbolicFold s, BaseField s ~ BaseField c) =>
      s f -> p (WitnessField s) -> s g -> (s f, p (WitnessField s))) ->
    c f -> p wc -> c h -> Infinite (g wc) -> c Par1 -> (c f, p wc)
