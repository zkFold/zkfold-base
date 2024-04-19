{-# LANGUAGE DeriveAnyClass, UndecidableInstances #-}

module ZkFold.Symbolic.Data.Bool (
    BoolType(..),
    Bool(..),
    all,
    all1,
    any
) where

import           Data.Distributive               (Distributive (..))
import           Data.Functor.Rep
import           GHC.Generics                    (Generic1)
import           Numeric.Natural                 (Natural)
import           Prelude                         hiding (Bool, Num (..), all, any, not, (&&), (/), (||))
import qualified Prelude                         as Haskell

import           ZkFold.Base.Algebra.Basic.Class

class BoolType b where
    true  :: b

    false :: b

    not   :: b -> b

    (&&)  :: b -> b -> b

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
    deriving stock (Eq, Functor, Foldable, Traversable, Generic1)
    deriving anyclass (Representable)
instance Distributive Bool where
    distribute = distributeRep
    collect = collectRep
deriving via Representably Bool instance
  Field x => VectorSpace x Bool
deriving via Representably Bool x instance
  AdditiveSemigroup x => AdditiveSemigroup (Bool x)
deriving via Representably Bool x instance
  AdditiveMonoid x => AdditiveMonoid (Bool x)
deriving via Representably Bool x instance
  AdditiveGroup x => AdditiveGroup (Bool x)
deriving via Representably Bool x instance
  Scale Natural x => Scale Natural (Bool x)
deriving via Representably Bool x instance
  Scale Integer x => Scale Integer (Bool x)
deriving via Representably Bool x instance
  MultiplicativeMonoid x => Scale x (Bool x)

instance (Field x, Eq x) => Show (Bool x) where
    show (Bool x) = if x == one then "True" else "False"

instance Field x => BoolType (Bool x) where
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
