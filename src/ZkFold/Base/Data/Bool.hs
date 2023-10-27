module ZkFold.Base.Data.Bool (
    BoolType(..),
    Bool(..),
    all,
    any
) where

import           Prelude                                      hiding (Num(..), Bool, (/), (&&), (||), not, all, any)
import qualified Prelude                                      as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Protocol.Arithmetization         (Arithmetizable (..))

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

-- TODO: hide this constructor
newtype Bool x = Bool x
    deriving (Show, Eq)

instance FiniteField x => BoolType (Bool x) where
    true = Bool one

    false = Bool zero

    not (Bool b) = Bool $ one - b

    (&&) (Bool b1) (Bool b2) = Bool $ b1 * b2

    (||) (Bool b1) (Bool b2) = Bool $ b1 + b2 - b1 * b2

all :: BoolType b => (x -> b) -> [x] -> b
all f = foldr ((&&) . f) true

any :: BoolType b => (x -> b) -> [x] -> b
any f = foldr ((||) . f) false

instance Arithmetizable a x => Arithmetizable a (Bool x) where
    arithmetize (Bool b) = arithmetize b

    restore [r] = Bool $ restore [r]
    restore _   = error "SymbolicBool: invalid number of values"

    typeSize = 1