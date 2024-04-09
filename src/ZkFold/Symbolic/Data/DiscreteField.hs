module ZkFold.Symbolic.Data.DiscreteField where

import Data.Bool (bool)
import ZkFold.Base.Algebra.Basic.Class
import ZkFold.Base.Algebra.Basic.Field (Zp)
import ZkFold.Base.Algebra.Basic.Number (Prime)
import ZkFold.Symbolic.Data.Bool (Bool (..), BoolType (..))
import Prelude hiding (Bool)
import qualified Prelude as Haskell

class (BoolType b, Field a) => DiscreteField b a where
  isZero :: a -> b

instance (Field a, Eq a) => DiscreteField Haskell.Bool a where
  isZero = (== zero)

instance (Prime p, Field x, Eq x) => DiscreteField (Bool (Zp p)) x where
  isZero = Bool . bool zero one . (== zero)
