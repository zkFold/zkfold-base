module Examples.Constant (exampleConst5, exampleEq5) where

import           Examples.Eq                       (exampleEq)

import           ZkFold.Base.Algebra.Basic.Class   (FromConstant (..))
import           ZkFold.Base.Algebra.Basic.Number  (Natural)
import           ZkFold.Symbolic.Class             (Symbolic)
import           ZkFold.Symbolic.Data.Bool         (Bool)
import           ZkFold.Symbolic.Data.FieldElement (FieldElement)

exampleConst5 :: Symbolic c => FieldElement c
exampleConst5 = fromConstant (5 :: Natural)

exampleEq5 :: Symbolic c => FieldElement c -> Bool c
exampleEq5 = exampleEq exampleConst5
