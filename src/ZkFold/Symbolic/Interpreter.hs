module ZkFold.Symbolic.Interpreter (Interpreter (..)) where

import           Control.DeepSeq                 (NFData)
import           Data.Eq                         (Eq)
import           Data.Function                   ((.))
import           Data.Functor                    ((<$>))
import           GHC.Generics                    (Generic)
import           Text.Show                       (Show)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector         (Vector, item, singleton)
import           ZkFold.Symbolic.Class

newtype Interpreter a n = Interpreter { runInterpreter :: Vector n a }
    deriving (Eq, Show, Generic, NFData)

instance Symbolic (Interpreter a) where
    type BaseField (Interpreter a) = a

value :: Interpreter a 1 -> a
value (Interpreter (item -> x)) = x

const :: a -> Interpreter a 1
const = Interpreter . singleton

instance MultiplicativeSemigroup a => MultiplicativeSemigroup (Interpreter a 1) where
  (value -> x) * (value -> y) = const (x * y)

instance Exponent a p => Exponent (Interpreter a 1) p where
  (value -> x) ^ p = const (x ^ p)

instance MultiplicativeMonoid a => MultiplicativeMonoid (Interpreter a 1) where
  one = const one

instance Scale c a => Scale c (Interpreter a 1) where
  scale k (value -> x) = const (scale k x)

instance AdditiveSemigroup a => AdditiveSemigroup (Interpreter a 1) where
  (value -> x) + (value -> y) = const (x + y)

instance AdditiveMonoid a => AdditiveMonoid (Interpreter a 1) where
  zero = const zero

instance AdditiveGroup a => AdditiveGroup (Interpreter a 1) where
  negate (value -> x) = const (negate x)
  (value -> x) - (value -> y) = const (x - y)

instance FromConstant c a => FromConstant c (Interpreter a 1) where
  fromConstant = const . fromConstant

instance Semiring a => Semiring (Interpreter a 1)

instance Ring a => Ring (Interpreter a 1)

instance Field a => Field (Interpreter a 1) where
  finv (value -> x) = const (finv x)
  (value -> x) // (value -> y) = const (x // y)
  rootOfUnity n = const <$> rootOfUnity n
