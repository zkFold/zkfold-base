module ZkFold.Symbolic.Class where

import           Data.Kind       (Type)
import           Numeric.Natural (Natural)

class Symbolic (c :: Natural -> Type) where
    type BaseField c :: Type
