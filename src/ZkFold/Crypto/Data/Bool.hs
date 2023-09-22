module ZkFold.Crypto.Data.Bool (
    GeneralizedBoolean(..),
    SymbolicBool(..)
) where

import           Prelude                           hiding (Num(..), (/))

import           ZkFold.Crypto.Algebra.Basic.Class

class GeneralizedBoolean b where
    true  :: b
    
    false :: b

    not   :: b -> b

    (&&)  :: b -> b -> b

    (||)  :: b -> b -> b

instance GeneralizedBoolean Bool where
    true  = True

    false = False

    not   = Prelude.not

    (&&)  = (Prelude.&&)

    (||)  = (Prelude.||)

-- TODO: hide this constructor
newtype SymbolicBool ctx = SymbolicBool ctx
    deriving (Show)

instance FiniteField ctx => GeneralizedBoolean (SymbolicBool ctx) where
    true = SymbolicBool one

    false = SymbolicBool zero

    not (SymbolicBool b) = SymbolicBool $ one - b

    (&&) (SymbolicBool b1) (SymbolicBool b2) = SymbolicBool $ b1 * b2

    (||) (SymbolicBool b1) (SymbolicBool b2) = SymbolicBool $ b1 + b2 - b1 * b2