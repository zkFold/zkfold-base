module ZkFold.Symbolic.Data.Conditional where

import           Data.Function                     (($), (.))
import           Data.Zip                          (zipWith)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector           (item)
import           ZkFold.Symbolic.Data.Bool         (Bool (Bool))
import           ZkFold.Symbolic.Data.FieldElement
import           ZkFold.Symbolic.Interpreter       (Interpreter (..))

class Conditional b a where
    bool :: a -> a -> b -> a

    gif :: b -> a -> a -> a
    gif b x y = bool y x b

    (?) :: b -> a -> a -> a
    (?) = gif

instance (Ring a, FieldElementData (Interpreter a) x) => Conditional (Bool (Interpreter a)) x where
    bool x y (Bool (Interpreter b)) =
      let b' = item b
       in fromFieldElements . Interpreter $ zipWith (\x' y' -> (one - b') * x' + b' * y')
              (runInterpreter $ toFieldElements x)
              (runInterpreter $ toFieldElements y)
