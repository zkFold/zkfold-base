module ZkFold.Symbolic.Interpreter (Interpreter (..), mapInterpreter) where

import           Control.DeepSeq                 (NFData)
import           Data.Eq                         (Eq)
import           Data.Function                   ((.))
import           Data.Functor                    ((<$>))
import           GHC.Generics                    (Generic, Par1 (Par1))
import           Text.Show                       (Show)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Class

newtype Interpreter a f = Interpreter { runInterpreter :: f a }
    deriving (Eq, Show, Generic, NFData)

instance Symbolic (Interpreter a) where
    type BaseField (Interpreter a) = a

mapInterpreter :: (forall i . f i -> g i) -> Interpreter a f -> Interpreter a g
mapInterpreter f (Interpreter x) = Interpreter (f x)

value :: Interpreter a Par1 -> a
value (Interpreter (Par1 x)) = x

const :: a -> Interpreter a Par1
const = Interpreter . Par1

instance MultiplicativeSemigroup a => MultiplicativeSemigroup (Interpreter a Par1) where
  (value -> x) * (value -> y) = const (x * y)

instance Exponent a p => Exponent (Interpreter a Par1) p where
  (value -> x) ^ p = const (x ^ p)

instance MultiplicativeMonoid a => MultiplicativeMonoid (Interpreter a Par1) where
  one = const one

instance Scale c a => Scale c (Interpreter a Par1) where
  scale k (value -> x) = const (scale k x)

instance AdditiveSemigroup a => AdditiveSemigroup (Interpreter a Par1) where
  (value -> x) + (value -> y) = const (x + y)

instance AdditiveMonoid a => AdditiveMonoid (Interpreter a Par1) where
  zero = const zero

instance AdditiveGroup a => AdditiveGroup (Interpreter a Par1) where
  negate (value -> x) = const (negate x)
  (value -> x) - (value -> y) = const (x - y)

instance FromConstant c a => FromConstant c (Interpreter a Par1) where
  fromConstant = const . fromConstant

instance Semiring a => Semiring (Interpreter a Par1)

instance Ring a => Ring (Interpreter a Par1)

instance Field a => Field (Interpreter a Par1) where
  finv (value -> x) = const (finv x)
  (value -> x) // (value -> y) = const (x // y)
  rootOfUnity n = const <$> rootOfUnity n
