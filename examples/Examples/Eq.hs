module Examples.Eq (exampleEq) where

import           ZkFold.Symbolic.Class             (Symbolic)
import           ZkFold.Symbolic.Data.Bool         (Bool)
import           ZkFold.Symbolic.Data.Eq           (Eq (..))
import           ZkFold.Symbolic.Data.FieldElement (FieldElement)

-- | (==) operation
exampleEq :: Symbolic c => FieldElement c -> FieldElement c -> Bool c
exampleEq x y = x == y
