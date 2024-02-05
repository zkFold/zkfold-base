module ZkFold.Symbolic.Data.DiscreteField where

import           Control.Monad.State                                    (evalState)
import           Data.Bool                                              (bool)
import           Prelude                                                hiding (Bool)
import qualified Prelude                                                as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                        (Zp)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (isZeroC)
import           ZkFold.Symbolic.Data.Bool                              (Bool (..), BoolType (..))

class (BoolType b, Field a) => DiscreteField b a where
    isZero :: a -> b

instance (Field a, Eq a) => DiscreteField Haskell.Bool a where
    isZero = (== zero)

instance (Prime p, Field x, Eq x) => DiscreteField (Bool (Zp p)) x where
    isZero = Bool . bool zero one . (== zero)

instance (Arithmetizable a x, Field x) => DiscreteField (Bool (ArithmeticCircuit a)) x where
    isZero x = case evalState (arithmetize x) mempty of
      [] -> true
      xs -> Bool $ product1 (map isZeroC xs)
