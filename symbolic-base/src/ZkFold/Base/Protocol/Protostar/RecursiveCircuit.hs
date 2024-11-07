module ZkFold.Base.Protocol.Protostar.RecursiveCircuit where

import           Prelude                                          (undefined)

import           ZkFold.Base.Data.Vector                          (Vector)
import           ZkFold.Base.Protocol.Protostar.ArithmeticCircuit ()
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.FieldElement                (FieldElement(..))

-- | Takes a function `f` and returns a circuit `C` with inputs `y` and `w`.
-- The circuit is such that `C(y, w) = 0` implies that `y` belongs to the image of `f^n` for some positive `n`.
protostar :: forall a n .
       (forall ctx . Symbolic ctx => Vector n (FieldElement ctx) -> Vector n (FieldElement ctx))
    -> ArithmeticCircuit a (Vector n) (Vector n)
protostar _ =
    let circuit = undefined
    in circuit