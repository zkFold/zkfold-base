{-# LANGUAGE DerivingStrategies #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Witness where

import           Data.Function                   ((.))
import           Numeric.Natural                 (Natural)
import           Prelude                         (Integer)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.MonadCircuit    (ResidueField, Witness (..))

type IsWitness a n w = (Scale a w, FromConstant a w, ResidueField n w)

newtype WitnessF v a = WitnessF { witnessF :: forall n w. IsWitness a n w => (v -> w) -> w }

instance FromConstant Natural (WitnessF v a) where fromConstant x = WitnessF (fromConstant x)
instance FromConstant Integer (WitnessF v a) where fromConstant x = WitnessF (fromConstant x)
instance FromConstant a (WitnessF v a) where fromConstant x = WitnessF (fromConstant x)
instance Scale Natural (WitnessF v a) where scale k (WitnessF f) = WitnessF (scale k f)
instance Scale Integer (WitnessF v a) where scale k (WitnessF f) = WitnessF (scale k f)
instance Scale a (WitnessF v a) where scale k (WitnessF f) = WitnessF (scale k . f)
instance Exponent (WitnessF v a) Natural where WitnessF f ^ p = WitnessF (f ^ p)
instance Exponent (WitnessF v a) Integer where WitnessF f ^ p = WitnessF (f ^ p)
instance AdditiveSemigroup (WitnessF v a) where WitnessF f + WitnessF g = WitnessF (f + g)
instance AdditiveMonoid (WitnessF v a) where zero = WitnessF zero
instance AdditiveGroup (WitnessF v a) where
  negate (WitnessF f) = WitnessF (negate f)
  WitnessF f - WitnessF g = WitnessF (f - g)
instance MultiplicativeSemigroup (WitnessF v a) where WitnessF f * WitnessF g = WitnessF (f * g)
instance MultiplicativeMonoid (WitnessF v a) where one = WitnessF one
instance Semiring (WitnessF v a)
instance Ring (WitnessF v a)
instance Field (WitnessF v a) where
  finv (WitnessF f) = WitnessF (finv . f)
  WitnessF f // WitnessF g = WitnessF (\x -> f x // g x)
instance ToConstant (WitnessF v a) where
  type Const (WitnessF v a) = EuclideanF v a
  toConstant (WitnessF f) = EuclideanF (toConstant . f)
instance FromConstant (EuclideanF v a) (WitnessF v a) where fromConstant (EuclideanF f) = WitnessF (fromConstant . f)
instance Finite a => Finite (WitnessF v a) where type Order (WitnessF v a) = Order a

newtype EuclideanF v a = EuclideanF { euclideanF :: forall n w. IsWitness a n w => (v -> w) -> n }

instance FromConstant Natural (EuclideanF v a) where fromConstant x = EuclideanF (fromConstant x)
instance Scale Natural (EuclideanF v a) where scale k (EuclideanF f) = EuclideanF (scale k f)
instance Exponent (EuclideanF v a) Natural where EuclideanF f ^ p = EuclideanF (f ^ p)
instance AdditiveSemigroup (EuclideanF v a) where EuclideanF f + EuclideanF g = EuclideanF (f + g)
instance AdditiveMonoid (EuclideanF v a) where zero = EuclideanF zero
instance MultiplicativeSemigroup (EuclideanF v a) where EuclideanF f * EuclideanF g = EuclideanF (f * g)
instance MultiplicativeMonoid (EuclideanF v a) where one = EuclideanF one
instance Semiring (EuclideanF v a)
instance SemiEuclidean (EuclideanF v a) where
  EuclideanF f `div` EuclideanF g = EuclideanF (\x -> f x `div` g x)
  EuclideanF f `mod` EuclideanF g = EuclideanF (\x -> f x `mod` g x)

instance Finite a => Witness v (WitnessF v a) where
  at i = WitnessF (\x -> x i)
