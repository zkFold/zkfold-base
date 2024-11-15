{-# LANGUAGE DerivingStrategies #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Witness where

import           Control.Applicative             (Applicative (..))
import           Control.DeepSeq                 (NFData (..), rwhnf)
import           Control.Monad                   (Monad (..), ap)
import           Data.Function                   ((.))
import           Data.Functor                    (Functor)
import           Numeric.Natural                 (Natural)
import           Prelude                         (Integer)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.MonadCircuit    (ResidueField)

type IsWitness a n w = (Scale a w, FromConstant a w, ResidueField n w)

newtype WitnessF a v = WitnessF { runWitnessF :: forall n w. IsWitness a n w => (v -> w) -> w }
  deriving (Functor)

instance NFData (WitnessF a v) where
  -- From instance NFData (a -> b):
  -- This instance is for convenience and consistency with seq.
  -- This assumes that WHNF is equivalent to NF for functions.
  rnf = rwhnf

instance Applicative (WitnessF a) where
  pure v = WitnessF (\x -> x v)
  (<*>) = ap

instance Monad (WitnessF a) where
  WitnessF f >>= k = WitnessF (\x -> f (\a -> runWitnessF (k a) x))

instance FromConstant Natural (WitnessF a v) where fromConstant x = WitnessF (fromConstant x)
instance FromConstant Integer (WitnessF a v) where fromConstant x = WitnessF (fromConstant x)
instance FromConstant a (WitnessF a v) where fromConstant x = WitnessF (fromConstant x)
instance Scale Natural (WitnessF a v) where scale k (WitnessF f) = WitnessF (scale k f)
instance Scale Integer (WitnessF a v) where scale k (WitnessF f) = WitnessF (scale k f)
instance Scale a (WitnessF a v) where scale k (WitnessF f) = WitnessF (scale k . f)
instance Exponent (WitnessF a v) Natural where WitnessF f ^ p = WitnessF (f ^ p)
instance Exponent (WitnessF a v) Integer where WitnessF f ^ p = WitnessF (f ^ p)
instance AdditiveSemigroup (WitnessF a v) where WitnessF f + WitnessF g = WitnessF (f + g)
instance AdditiveMonoid (WitnessF a v) where zero = WitnessF zero
instance AdditiveGroup (WitnessF a v) where
  negate (WitnessF f) = WitnessF (negate f)
  WitnessF f - WitnessF g = WitnessF (f - g)
instance MultiplicativeSemigroup (WitnessF a v) where WitnessF f * WitnessF g = WitnessF (f * g)
instance MultiplicativeMonoid (WitnessF a v) where one = WitnessF one
instance Semiring (WitnessF a v)
instance Ring (WitnessF a v)
instance Field (WitnessF a v) where
  finv (WitnessF f) = WitnessF (finv . f)
  WitnessF f // WitnessF g = WitnessF (\x -> f x // g x)
instance ToConstant (WitnessF a v) where
  type Const (WitnessF a v) = EuclideanF a v
  toConstant (WitnessF f) = EuclideanF (toConstant . f)
instance FromConstant (EuclideanF a v) (WitnessF a v) where fromConstant (EuclideanF f) = WitnessF (fromConstant . f)
instance Finite a => Finite (WitnessF a v) where type Order (WitnessF a v) = Order a

newtype EuclideanF a v = EuclideanF { euclideanF :: forall n w. IsWitness a n w => (v -> w) -> n }

instance FromConstant Natural (EuclideanF a v) where fromConstant x = EuclideanF (fromConstant x)
instance Scale Natural (EuclideanF a v) where scale k (EuclideanF f) = EuclideanF (scale k f)
instance Exponent (EuclideanF a v) Natural where EuclideanF f ^ p = EuclideanF (f ^ p)
instance AdditiveSemigroup (EuclideanF a v) where EuclideanF f + EuclideanF g = EuclideanF (f + g)
instance AdditiveMonoid (EuclideanF a v) where zero = EuclideanF zero
instance MultiplicativeSemigroup (EuclideanF a v) where EuclideanF f * EuclideanF g = EuclideanF (f * g)
instance MultiplicativeMonoid (EuclideanF a v) where one = EuclideanF one
instance Semiring (EuclideanF a v)
instance SemiEuclidean (EuclideanF a v) where
  EuclideanF f `div` EuclideanF g = EuclideanF (\x -> f x `div` g x)
  EuclideanF f `mod` EuclideanF g = EuclideanF (\x -> f x `mod` g x)
