{-# LANGUAGE
DerivingStrategies
, DerivingVia
, UndecidableInstances
#-}

module ZkFold.Symbolic.Data.Bool (
    Bool (Bool),
    Boolean (..),
    bool,
    ifThenElse,
    (?),
    Eq (..),
    (/=)
) where

import           Data.Functor.Identity                 (Identity (..))
import qualified Prelude                               as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.VectorSpace
import           ZkFold.Symbolic.Types                 (Symbolic)

-- TODO (Issue #18): hide this constructor
newtype Bool a = Bool a
  deriving stock
    ( Haskell.Functor
    , Haskell.Foldable
    , Haskell.Traversable
    )
deriving via Identity instance VectorSpace a Bool
instance (Symbolic a, Haskell.Eq a) => Haskell.Show (Bool a) where
    show (Bool a) = if a Haskell.== one then "true" else "false"

class Boolean a b where
  true :: b a
  false :: b a
  not :: b a -> b a
  infixr 3 &&
  (&&) :: b a -> b a -> b a
  infixr 2 ||
  (||) :: b a -> b a -> b a
  xor :: b a -> b a -> b a

instance Symbolic a => Boolean a Bool where
  true = Bool one
  false = Bool zero
  not (Bool b) = Bool (one - b)
  Bool b1 && Bool b2 = Bool (b1 * b2)
  Bool b1 || Bool b2 = Bool (b1 + b2 - b1 * b2)
  xor (Bool b1) (Bool b2) = Bool (b1 + b2 - (b1 * b2 + b1 * b2))

bool :: (Symbolic a, VectorSpace a u) => u a -> u a -> Bool a -> u a
bool f t (Bool b) = scaleV b (t `subtractV` f) `addV` f

ifThenElse, (?)
  :: (Symbolic a, VectorSpace a u) => Bool a -> u a -> u a -> u a
ifThenElse b t f = bool f t b
(?) = ifThenElse

class Eq a u where
    infix 4 ==
    (==) :: Symbolic a => u a -> u a -> Bool a
    default (==)
      :: (Symbolic a, Haskell.Foldable u, VectorSpace a u)
      => u a -> u a -> Bool a
    u == v = Bool (Haskell.foldl (*) one (zipWithV equal u v))
instance Eq a Bool

infix 4 /=
(/=) :: (Symbolic a, Eq a u) => u a -> u a -> Bool a
u /= b = not (u == b)
