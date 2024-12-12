{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.WitnessEstimation where



import           Control.Applicative                            ()
import           Data.Functor.Rep                               (Rep)
import           GHC.Generics                                   (Generic)
import           GHC.Integer                                    (Integer)
import           GHC.Natural                                    (Natural)
import           Prelude                                        (Eq, error, ($), (.), (==))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.ByteString                    ()
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Var



data UVar a i
  = ConstUVar a
  | LinUVar a (SysVar i) a
  | More
  deriving Generic

instance FromConstant a (UVar a i) where
    fromConstant = ConstUVar
instance FromConstant Natural a => FromConstant Natural (UVar a i) where fromConstant = ConstUVar . fromConstant
instance FromConstant Integer a => FromConstant Integer (UVar a i) where fromConstant = ConstUVar . fromConstant

instance (MultiplicativeSemigroup a, Eq a, AdditiveMonoid a) => Scale a (UVar a i) where
  scale k (ConstUVar c) = ConstUVar $ k * c
  scale k (LinUVar a x b) = if k == zero
    then ConstUVar zero
    else LinUVar (k * a) x (k * b)
  scale k More = if k == zero
    then ConstUVar zero
    else More

instance Scale Natural (UVar a i) where scale k = scale k . fromConstant
instance Scale Integer (UVar a i) where scale k = scale k . fromConstant

instance (Exponent a Natural, MultiplicativeMonoid a) => Exponent (UVar a i) Natural where
  (ConstUVar c) ^ n   = ConstUVar $ c ^ n
  (LinUVar k x b) ^ 1 = LinUVar k x b
  (LinUVar {}) ^ 0    = ConstUVar one
  _ ^ _               = More

instance (Exponent a Integer, MultiplicativeMonoid a) => Exponent (UVar a i) Integer where
  (ConstUVar c) ^ n   = ConstUVar $ c ^ n
  (LinUVar k x b) ^ 1 = LinUVar k x b
  _ ^ 0               = ConstUVar one
  _ ^ _               = More

instance (AdditiveSemigroup a, AdditiveMonoid a, Eq a, Eq (Rep i)) => AdditiveSemigroup (UVar a i) where
  ConstUVar c1 + ConstUVar c2 = ConstUVar $ c1 + c2
  LinUVar k1 x1 b1 + (LinUVar k2 x2 b2) = if x1 == x2
    then if k1 + k2 == zero
      then ConstUVar $ b1 + b2
      else LinUVar (k1 + k2) x1 (b1 + b2)
    else More
  LinUVar k x b + ConstUVar c = LinUVar k x (b + c)
  ConstUVar c + LinUVar k x b = LinUVar k x (b + c)
  _ + _ = More

instance (AdditiveMonoid a, Eq a, Eq (Rep i)) => AdditiveMonoid (UVar a i) where
  zero = ConstUVar zero

instance (Eq a, AdditiveMonoid a, Eq (Rep i), AdditiveGroup a) => AdditiveGroup (UVar a i) where
  negate (ConstUVar c)   = ConstUVar (negate c)
  negate (LinUVar k x b) = LinUVar (negate k) x (negate b)
  negate More            = More

instance (MultiplicativeSemigroup a, Eq a, AdditiveMonoid a, Eq (Rep i)) => MultiplicativeSemigroup (UVar a i) where
  ConstUVar c1 * ConstUVar c2 = ConstUVar $ c1 * c2
  ConstUVar c * (LinUVar k x b) = if c == zero
    then zero
    else LinUVar (c * k) x (c * b)
  (LinUVar k x b) * (ConstUVar c) = if c == zero
    then zero
    else LinUVar (c * k) x (c * b)
  _ * _ = More

instance (MultiplicativeMonoid a, AdditiveMonoid a, Eq a, Eq (Rep i)) => MultiplicativeMonoid (UVar a i) where
  one = ConstUVar one

instance (AdditiveMonoid a, Eq a, Eq (Rep i), FromConstant Natural a, MultiplicativeMonoid a) => Semiring (UVar a i)

instance (AdditiveMonoid a, Eq a, Eq (Rep i), AdditiveGroup a, FromConstant Natural a, FromConstant Integer a, MultiplicativeMonoid a) => Ring (UVar a i)

instance (AdditiveMonoid a, Eq a, Eq (Rep i), AdditiveGroup a, FromConstant Natural a, FromConstant Integer a, MultiplicativeMonoid a, Field a) => Field (UVar a i) where
  finv (ConstUVar c) = ConstUVar $ finv c
  finv _             = More

instance (ToConstant a) => ToConstant (UVar a i) where
  type Const (UVar a i) = Const a
  toConstant (ConstUVar c) = toConstant c
  toConstant _             = error "WitnessEstimation: this should`t happen"

instance Finite a => Finite (UVar a i) where type Order (UVar a i) = Order a
