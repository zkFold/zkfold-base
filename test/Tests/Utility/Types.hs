module Tests.Utility.Types (SmallField) where

import           ZkFold.Crypto.Algebra.Basic.Class (Finite(..), Prime)

data SmallField
instance Finite SmallField where
    order = 97
instance Prime SmallField