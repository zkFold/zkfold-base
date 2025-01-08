{-# LANGUAGE TypeOperators #-}

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
    (Representable f, NFData1 f, Traversable f) =>
    (Binary (Rep g), NFData (Rep g), Ord (Rep g), Representable g) =>
    (forall s. (Symbolic s, BaseField s ~ BaseField c) => s f -> s g -> s f) ->
    c f -> Infinite (g (WitnessField c)) -> c Par1 -> c f
