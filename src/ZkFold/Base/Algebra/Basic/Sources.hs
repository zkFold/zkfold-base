{-# LANGUAGE DerivingStrategies #-}

module ZkFold.Base.Algebra.Basic.Sources (Sources (..)) where

import           Data.Function                   (const, id)
import           Data.Kind                       (Type)
import           Data.Maybe                      (Maybe (..))
import           Data.Monoid                     (Monoid (..))
import           Data.Ord                        (Ord)
import           Data.Semigroup                  (Semigroup (..))
import           Data.Set                        (Set)
import qualified Data.Set                        as Set
import           Numeric.Natural                 (Natural)
import           Prelude                         (Integer)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Prelude

newtype Sources a i = Sources { runSources :: Set i }
    deriving newtype (Semigroup, Monoid)

empty :: Sources a i
empty = Sources Set.empty

instance {-# OVERLAPPING #-} FromConstant (Sources a i) (Sources a i) where
  fromConstant = id

instance {-# OVERLAPPING #-} Ord i => Scale (Sources a i) (Sources a i) where
  scale = (<>)

instance {-# OVERLAPPABLE #-} FromConstant c (Sources a i) where
  fromConstant = const empty

instance {-# OVERLAPPABLE #-} MultiplicativeMonoid c => Scale c (Sources a i) where
  scale = const id

instance Ord i => AdditiveSemigroup (Sources a i) where
  (+) = (<>)

instance Ord i => AdditiveMonoid (Sources a i) where
  zero = mempty

instance Ord i => AdditiveGroup (Sources a i) where
  negate = id

instance Finite a => Finite (Sources a i) where
  type Order (Sources a i) = Order a

instance Ord i => MultiplicativeSemigroup (Sources a i) where
  (*) = (<>)

instance Exponent (Sources a i) Natural where
  (^) = const

instance Ord i => MultiplicativeMonoid (Sources a i) where
  one = mempty

instance Exponent (Sources a i) Integer where
  (^) = const

instance Ord i => MultiplicativeGroup (Sources a i) where
  invert = id

instance Ord i => Semiring (Sources a i)

instance Ord i => Ring (Sources a i)

instance Ord i => Field (Sources a i) where
  finv = id
  rootOfUnity _ = Just mempty

instance ToConstant (Sources (a :: Type) i) where
  type Const (Sources a i) = Sources a i
  toConstant = id

instance (Finite a, Ord i) => BinaryExpansion (Sources a i) where
  type Bits (Sources a i) = [Sources a i]
  binaryExpansion = replicate (numberOfBits @a)

instance Ord i => EuclideanDomain (Sources a i) where
  div = (<>)
  mod = (<>)
