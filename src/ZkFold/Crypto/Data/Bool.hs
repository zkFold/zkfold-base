{-# LANGUAGE TypeApplications #-}

module ZkFold.Crypto.Data.Bool (
    GeneralizedBoolean(..),
    SymbolicBool(..),
    all,
    any
) where

import           Prelude                           hiding (Num(..), (/), (&&), (||), not, all, any)
import qualified Prelude                           as Haskell

import           ZkFold.Crypto.Algebra.Basic.Class
import ZkFold.Crypto.Data.Symbolic (Symbolic(..))

class GeneralizedBoolean b where
    true  :: b

    false :: b

    not   :: b -> b

    (&&)  :: b -> b -> b

    (||)  :: b -> b -> b

instance GeneralizedBoolean Bool where
    true  = True

    false = False

    not   = Haskell.not

    (&&)  = (Haskell.&&)

    (||)  = (Haskell.||)

-- TODO: hide this constructor
newtype SymbolicBool ctx = SymbolicBool ctx
    deriving (Show, Eq)

instance Symbolic ctx ctx Integer => Symbolic ctx (SymbolicBool ctx) Integer where
    fromValue (SymbolicBool b) = fromValue @ctx @ctx @Integer b

    toValue = SymbolicBool . toValue @ctx @ctx @Integer

    fromSymbol = fromSymbol @ctx @ctx

    toSymbol = toSymbol @ctx @ctx

    symbolSize = symbolSize @ctx @ctx @Integer


instance FiniteField ctx => GeneralizedBoolean (SymbolicBool ctx) where
    true = SymbolicBool one

    false = SymbolicBool zero

    not (SymbolicBool b) = SymbolicBool $ one - b

    (&&) (SymbolicBool b1) (SymbolicBool b2) = SymbolicBool $ b1 * b2

    (||) (SymbolicBool b1) (SymbolicBool b2) = SymbolicBool $ b1 + b2 - b1 * b2

all :: GeneralizedBoolean b => (a -> b) -> [a] -> b
all f = foldr ((&&) . f) true

any :: GeneralizedBoolean b => (a -> b) -> [a] -> b
any f = foldr ((||) . f) false