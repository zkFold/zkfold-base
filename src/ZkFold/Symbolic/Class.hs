module ZkFold.Symbolic.Class where

import           Data.Kind       (Type)

class Symbolic (c :: (Type -> Type) -> Type) where
    type BaseField c :: Type
