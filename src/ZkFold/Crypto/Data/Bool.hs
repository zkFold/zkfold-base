{-# LANGUAGE TypeApplications #-}

module ZkFold.Crypto.Data.Bool (
    GeneralizedBoolean(..),
    SymbolicBool(..),
    toBool,
    fromBool,
    all,
    any
) where

import           Data.Bool                          (bool)
import           Prelude                            hiding (Num(..), (/), (&&), (||), not, all, any)
import qualified Prelude                            as Haskell

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Data.Arithmetization (Arithmetization(..))
import           ZkFold.Crypto.Data.Symbolic        (Symbolic(..))

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

toBool :: (FiniteField ctx, Eq ctx) => SymbolicBool ctx -> Bool
toBool (SymbolicBool b) = bool False True $ b == one

fromBool :: (FiniteField ctx) => Bool -> SymbolicBool ctx
fromBool True  = SymbolicBool one
fromBool False = SymbolicBool zero

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

instance Symbolic ctx ctx Integer => Symbolic ctx (SymbolicBool ctx) Integer where
    fromValue (SymbolicBool b) = fromValue @ctx @ctx @Integer b

    toValue = SymbolicBool . toValue @ctx @ctx @Integer

    fromSymbol = fromSymbol @ctx @ctx

    toSymbol = toSymbol @ctx @ctx

    symbolSize = symbolSize @ctx @ctx @Integer

instance Arithmetization ctx ctx => Arithmetization ctx (SymbolicBool ctx) where
    type ValueOf (SymbolicBool ctx) = SymbolicBool (ValueOf ctx)

    type InputOf (SymbolicBool ctx) = InputOf ctx

    type Constraint ctx (SymbolicBool ctx) = Constraint ctx ctx

    merge (SymbolicBool b) = merge @ctx @ctx b

    atomic = atomic @ctx @ctx

    constraint = constraint @ctx @ctx

    assignment a = 
        let f x = let SymbolicBool b' = a x in b'
        in assignment @ctx @ctx f

    eval ctx = SymbolicBool . eval @ctx @ctx ctx

    input = fmap SymbolicBool (input @ctx @ctx)

    current = fmap SymbolicBool (current @ctx @ctx)

    apply (SymbolicBool b) = apply @ctx @ctx b