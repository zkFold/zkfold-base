{-# LANGUAGE TypeApplications #-}

module ZkFold.Crypto.Data.Bool (
    GeneralizedBoolean(..),
    SymbolicBool(..),
    toBool,
    fromBool,
    all,
    any
) where

import           Data.Bool                                    (bool)
import           Prelude                                      hiding (Num(..), (/), (&&), (||), not, all, any)
import qualified Prelude                                      as Haskell

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Data.Symbolic                 (Symbolic(..))
import           ZkFold.Crypto.Protocol.Arithmetization.R1CS (Arithmetization (..))

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
newtype SymbolicBool a = SymbolicBool a
    deriving (Show, Eq)

toBool :: (FiniteField a, Eq a) => SymbolicBool a -> Bool
toBool (SymbolicBool b) = bool False True $ b == one

fromBool :: FiniteField a => Bool -> SymbolicBool a
fromBool True  = SymbolicBool one
fromBool False = SymbolicBool zero

instance FiniteField a => GeneralizedBoolean (SymbolicBool a) where
    true = SymbolicBool one

    false = SymbolicBool zero

    not (SymbolicBool b) = SymbolicBool $ one - b

    (&&) (SymbolicBool b1) (SymbolicBool b2) = SymbolicBool $ b1 * b2

    (||) (SymbolicBool b1) (SymbolicBool b2) = SymbolicBool $ b1 + b2 - b1 * b2

all :: GeneralizedBoolean b => (a -> b) -> [a] -> b
all f = foldr ((&&) . f) true

any :: GeneralizedBoolean b => (a -> b) -> [a] -> b
any f = foldr ((||) . f) false

instance Symbolic a a Integer => Symbolic a (SymbolicBool a) Integer where
    fromValue (SymbolicBool b) = fromValue b

    toValue = SymbolicBool . toValue

    fromSymbol = fromSymbol @a @a

    toSymbol = toSymbol @a @a

    symbolSize = symbolSize @a @a @Integer

instance Arithmetization a t s x => Arithmetization a t s (SymbolicBool x) where
    merge (SymbolicBool b) = merge b