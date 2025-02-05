module Examples.Ed25519 (
    exampleEd25519Scale
  ) where

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Class             (Symbolic)
import           ZkFold.Symbolic.Data.Ed25519
import           ZkFold.Symbolic.Data.FieldElement

exampleEd25519Scale
    :: Symbolic c
    => FieldElement c
    -> Ed25519_Point c
    -> Ed25519_Point c
exampleEd25519Scale = scale
