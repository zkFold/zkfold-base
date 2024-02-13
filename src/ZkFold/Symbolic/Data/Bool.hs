module ZkFold.Symbolic.Data.Bool (
    BoolType(..),
    Bool(..),
    all,
    all1,
    any
) where

import           Prelude                         hiding (Num(..), Bool, (/), (&&), (||), not, all, any)
import qualified Prelude                         as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Compiler

class BoolType b where
    true  :: b

    false :: b

    not   :: b -> b

    (&&)  :: b -> b -> b

    (||)  :: b -> b -> b

instance BoolType Haskell.Bool where
    true  = True

    false = False

    not   = Haskell.not

    (&&)  = (Haskell.&&)

    (||)  = (Haskell.||)

-- TODO (Issue #18): hide this constructor
newtype Bool x = Bool x
    deriving (Eq)
instance (Field x, Eq x) => Show (Bool x) where
    show (Bool x) = if x == one then "True" else "False"

instance FiniteField x => BoolType (Bool x) where
    true = Bool one

    false = Bool zero

    not (Bool b) = Bool $ one - b

    (&&) (Bool b1) (Bool b2) = Bool $ b1 * b2

    (||) (Bool b1) (Bool b2) = Bool $ b1 + b2 - b1 * b2

all :: BoolType b => (x -> b) -> [x] -> b
all f = foldr ((&&) . f) true

all1 :: BoolType b => (x -> b) -> [x] -> b
all1 f = foldr1 (&&) . map f

any :: BoolType b => (x -> b) -> [x] -> b
any f = foldr ((||) . f) false

instance Arithmetic a => Arithmetizable a (Bool (ArithmeticCircuit a)) where
    arithmetize (Bool b) = arithmetize b

    restore [r] = Bool $ restore [r]
    restore _   = error "SymbolicBool: invalid number of values"

    typeSize = 1
