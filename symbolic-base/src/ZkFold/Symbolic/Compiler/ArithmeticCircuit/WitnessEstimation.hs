{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.WitnessEstimation where



import           Control.Applicative             ()
import           GHC.Generics                    (Generic)
import           GHC.Integer                     (Integer)
import           GHC.Natural                     (Natural)
import           Prelude                         (Eq, Maybe (..), ($), (.), (==))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.ByteString     ()
import           ZkFold.Symbolic.Class           (Arithmetic)
import           ZkFold.Symbolic.MonadCircuit    (ResidueField (..))



data UVar a v
  = ConstUVar a
  | LinUVar a v a
  | More
  deriving Generic

instance FromConstant a (UVar a v) where
    fromConstant = ConstUVar
instance FromConstant Natural a => FromConstant Natural (UVar a v) where fromConstant = ConstUVar . fromConstant
instance FromConstant Integer a => FromConstant Integer (UVar a v) where fromConstant = ConstUVar . fromConstant

instance (Semiring a, Eq a) => Scale a (UVar a v) where
  scale k (ConstUVar c) = ConstUVar $ k * c
  scale k (LinUVar a x b) = if k == zero
    then ConstUVar zero
    else LinUVar (k * a) x (k * b)
  scale k More = if k == zero
    then ConstUVar zero
    else More

instance (Semiring a, Eq a) => Scale Natural (UVar a v) where scale k = scale (fromConstant k :: a)
instance (Semiring a, Eq a, FromConstant Integer a) => Scale Integer (UVar a v) where scale k = scale (fromConstant k :: a)

instance MultiplicativeMonoid a => Exponent (UVar a v) Natural where
  (ConstUVar c) ^ n = ConstUVar $ c ^ n
  v ^ 1             = v
  _ ^ 0             = ConstUVar one
  _ ^ _             = More

instance (Exponent a Integer, MultiplicativeMonoid a) => Exponent (UVar a v) Integer where
  (ConstUVar c) ^ n   = ConstUVar $ c ^ n
  (LinUVar k x b) ^ 1 = LinUVar k x b
  _ ^ 0               = ConstUVar one
  _ ^ _               = More

instance (AdditiveMonoid a, Eq a, Eq v) => AdditiveSemigroup (UVar a v) where
  ConstUVar c + x = c .+ x
  x + ConstUVar c = c .+ x
  LinUVar k1 x1 b1 + (LinUVar k2 x2 b2) = if x1 == x2 then
    if k1 + k2 == zero
      then ConstUVar $ b1 + b2
      else LinUVar (k1 + k2) x1 (b1 + b2)
    else More
  _ + _ = More

(.+) :: AdditiveSemigroup a => a -> UVar a v -> UVar a v
c1 .+ ConstUVar c2 = ConstUVar $ c1 + c2
c .+ LinUVar k x b = LinUVar k x (b + c)
_ .+ More          = More

instance (Semiring a, Eq a, Eq v) => AdditiveMonoid (UVar a v) where
  zero = ConstUVar zero

instance (Ring a, Eq a, Eq v) => AdditiveGroup (UVar a v) where
  negate (ConstUVar c)   = ConstUVar (negate c)
  negate (LinUVar k x b) = LinUVar (negate k) x (negate b)
  negate More            = More

instance (Semiring a, Eq a) => MultiplicativeSemigroup (UVar a v) where
  ConstUVar c * x = scale c x
  x * ConstUVar c = scale c x
  _ * _           = More

instance (Semiring a, Eq a) => MultiplicativeMonoid (UVar a v) where
  one = ConstUVar one

instance (Semiring a, Eq a, Eq v) => Semiring (UVar a v)

instance (Ring a, Eq a, Eq v) => Ring (UVar a v)

instance (Field a, Eq a, Eq v) => Field (UVar a v) where
  finv (ConstUVar c) = ConstUVar $ finv c
  finv _             = More

instance Finite a => Finite (UVar a v) where type Order (UVar a v) = Order a

instance (Arithmetic a, Eq v) => ResidueField (UVar a v) where
  type IntegralOf (UVar a v) = Maybe Integer
  fromIntegral (Just x) = ConstUVar (fromConstant x)
  fromIntegral Nothing  = More
  toIntegral (ConstUVar c) = Just (toIntegral c)
  toIntegral _             = Nothing
