module ZkFold.Crypto.Data.Eq (
    GeneralizedEq(..)
) where

import           Prelude                              hiding (Num(..), (/=), (==), (/))
import qualified Prelude                              as Haskell

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Data.Bool              (SymbolicBool (..), GeneralizedBoolean)
import           ZkFold.Crypto.Data.Symbolic          (Symbolic(..))

class GeneralizedBoolean b => GeneralizedEq b a where
    (==) :: a -> a -> b

    (/=) :: a -> a -> b

instance Eq a => GeneralizedEq Bool a where
    x == y = x Haskell.== y
    x /= y = x Haskell./= y

instance (Symbolic ctx a, FiniteField ctx) => GeneralizedEq (SymbolicBool ctx) a where
    x == y =
        let z = compile x - compile y
        in SymbolicBool $ one - z / z

    x /= y =
        let z = compile x - compile y
        in SymbolicBool $ z / z