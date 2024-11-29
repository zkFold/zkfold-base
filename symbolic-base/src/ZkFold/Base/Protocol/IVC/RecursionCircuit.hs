module ZkFold.Base.Protocol.IVC.RecursionCircuit where

import           Prelude                                         hiding (Num (..), drop, head, replicate, take, zipWith)

import           ZkFold.Base.Data.Vector                         (Vector)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.FieldElement               (FieldElement (..))

-- | Takes a function `f` and returns a Protostar recursion circuit `R`.
ivcRecursionCircuit :: forall a payload input output nx nu . (forall ctx' . Symbolic ctx' => Vector nx (FieldElement ctx') -> Vector nu (FieldElement ctx') -> Vector nx (FieldElement ctx'))
    -> ArithmeticCircuit a payload input output
ivcRecursionCircuit _ = undefined