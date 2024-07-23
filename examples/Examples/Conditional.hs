module Examples.Conditional (exampleConditional) where

import           ZkFold.Symbolic.Class             (Symbolic)
import           ZkFold.Symbolic.Data.Bool         (Bool)
import           ZkFold.Symbolic.Data.Conditional  (Conditional (..))
import           ZkFold.Symbolic.Data.FieldElement (FieldElement)

exampleConditional ::
  Symbolic c => FieldElement c -> FieldElement c -> Bool c -> FieldElement c
exampleConditional = bool
