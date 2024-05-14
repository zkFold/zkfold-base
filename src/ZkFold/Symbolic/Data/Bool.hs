{-# LANGUAGE
DerivingStrategies
, DerivingVia
, UndecidableInstances
#-}

module ZkFold.Symbolic.Data.Bool (
    Bool(..),
    true,
    false,
    not,
    (&&),
    (||),
    xor,
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
  deriving stock Haskell.Foldable
deriving via Identity instance VectorSpace a Bool
instance Eq a Bool
instance (Symbolic a, Haskell.Eq a) => Haskell.Show (Bool a) where
    show (Bool a) = if a Haskell.== one then "true" else "false"

true :: Symbolic a => Bool a
true = Bool one

false :: Symbolic a => Bool a
false = Bool zero

not :: Symbolic a => Bool a -> Bool a
not (Bool b) = Bool (one - b)

(&&) :: Symbolic a => Bool a -> Bool a -> Bool a
Bool b1 && Bool b2 = Bool (b1 * b2)

(||) :: Symbolic a => Bool a -> Bool a -> Bool a
Bool b1 || Bool b2 = Bool (b1 + b2 - b1 * b2)

xor :: Symbolic a => Bool a -> Bool a -> Bool a
xor (Bool b1) (Bool b2) = Bool (b1 + b2 - (b1 * b2 + b1 * b2))

bool :: (Symbolic a, VectorSpace a u) => u a -> u a -> Bool a -> u a
bool f t (Bool b) = scaleV b (t `subtractV` f) `addV` f

ifThenElse, (?)
  :: (Symbolic a, VectorSpace a u) => Bool a -> u a -> u a -> u a
ifThenElse b t f = bool f t b
(?) = ifThenElse

class (VectorSpace a u, Haskell.Foldable u) => Eq a u where
    infix 4 ==
    (==) :: Symbolic a => u a -> u a -> Bool a
    u == v = Bool (Haskell.foldl (*) one (zipWithV equal u v))

infix 4 /=
(/=) :: (Symbolic a, Eq a u) => u a -> u a -> Bool a
u /= b = not (u == b)
