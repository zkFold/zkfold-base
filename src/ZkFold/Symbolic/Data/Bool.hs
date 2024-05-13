module ZkFold.Symbolic.Data.Bool (
    BoolType(..),
    Bool(..),
    all,
    all1,
    any
) where

import           Prelude                         hiding (Bool, Num (..), all, any, not, (&&), (/), (||))
import qualified Prelude                         as Haskell

import           ZkFold.Base.Algebra.Basic.Class

class BoolType b where
    true  :: b

    false :: b

    not   :: b -> b

    infixr 3 &&
    (&&)  :: b -> b -> b

    infixr 2 ||
    (||)  :: b -> b -> b

    xor  :: b -> b -> b

instance BoolType Haskell.Bool where
    true  = True

    false = False

    not   = Haskell.not

    (&&)  = (Haskell.&&)

    (||)  = (Haskell.||)

    xor = xor

-- TODO (Issue #18): hide this constructor
newtype Bool x = Bool x
    deriving (Eq)
instance (Field x, Eq x) => Show (Bool x) where
    show (Bool x) = if x == one then "True" else "False"

instance (Ring x) => BoolType (Bool x) where
    true = Bool one

    false = Bool zero

    not (Bool b) = Bool $ one - b

    (&&) (Bool b1) (Bool b2) = Bool $ b1 * b2

    (||) (Bool b1) (Bool b2) = Bool $ b1 + b2 - b1 * b2

    xor (Bool b1) (Bool b2) = Bool $ b1 + b2 - (b1 * b2 + b1 * b2)

all :: (BoolType b, Foldable t) => (x -> b) -> t x -> b
all f = foldr ((&&) . f) true

all1 :: (BoolType b, Functor t, Foldable t) => (x -> b) -> t x -> b
all1 f = foldr1 (&&) . fmap f

any :: (BoolType b, Foldable t) => (x -> b) -> t x -> b
any f = foldr ((||) . f) false
