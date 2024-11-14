module ZkFold.Symbolic.Data.DiscreteField where

import           Data.Bool                       (bool)
import           Prelude                         hiding (Bool)
import qualified Prelude                         as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Class           (Arithmetic)
import           ZkFold.Symbolic.Data.Bool       (Bool (..), BoolType (..))
import           ZkFold.Symbolic.Interpreter     (Interpreter)

class (BoolType b, Field a) => DiscreteField b a where
    isZero :: a -> b

instance (Field a, Eq a) => DiscreteField Haskell.Bool a where
    isZero = (== zero)

instance (Arithmetic a, Field x, Eq x) => DiscreteField (Bool (Interpreter a)) x where
    isZero = bool false true . (== zero)
