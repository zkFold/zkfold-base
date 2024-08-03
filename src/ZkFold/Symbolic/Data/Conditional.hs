module ZkFold.Symbolic.Data.Conditional where

import           Data.Function                   (($))
import           Data.Zip                        (zipWith)
import           GHC.Generics                    (Par1 (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Data.Bool       (Bool (Bool))
import           ZkFold.Symbolic.Data.Class
import           ZkFold.Symbolic.Interpreter     (Interpreter (..))

class Conditional b a where
    bool :: a -> a -> b -> a

    gif :: b -> a -> a -> a
    gif b x y = bool y x b

    (?) :: b -> a -> a -> a
    (?) = gif

instance (Ring a, SymbolicData (Interpreter a) x) => Conditional (Bool (Interpreter a)) x where
    bool x y (Bool (Interpreter (Par1 b))) =
       restore $ \i -> Interpreter $ zipWith (\x' y' -> (one - b) * x' + b * y')
          (runInterpreter $ pieces x i)
          (runInterpreter $ pieces y i)
