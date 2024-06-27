{-# LANGUAGE DerivingStrategies #-}

module ZkFold.Base.Algebra.Basic.Sources where

import           Data.Set                        (Set)
import           Prelude                         hiding (replicate)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Prelude

newtype Sources a i = Sources { runSources :: Set i }
    deriving newtype (Semigroup, Monoid)

instance MultiplicativeSemigroup c => Exponent (Sources a i) c where
  (^) = const

instance MultiplicativeMonoid c => Scale c (Sources a i) where
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

instance Ord i => MultiplicativeMonoid (Sources a i) where
  one = mempty

instance Ord i => MultiplicativeGroup (Sources a i) where
  invert = id

instance Ord i => FromConstant c (Sources a i) where
  fromConstant _ = mempty

instance Ord i => Semiring (Sources a i)

instance Ord i => Ring (Sources a i)

instance Ord i => Field (Sources a i) where
    finv = id
    rootOfUnity _ = Just (Sources mempty)

instance (Finite a, Ord i) => BinaryExpansion (Sources a i) [Sources a i] where
  binaryExpansion = replicate (numberOfBits @a)
