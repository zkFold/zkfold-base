{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Crypto.Algebra.Class where

import           Prelude (Integer)
import qualified Prelude as Haskell

infixl 7 *
infixl 6 +, -

class AdditiveSemigroup a where
    (+) :: a -> a -> a

class AdditiveSemigroup a => AdditiveMonoid a where
    zero :: a

class AdditiveMonoid a => AdditiveGroup a where
    {-# MINIMAL (negate | (-)) #-}
    (-) :: a -> a -> a
    x - y = x + negate y

    negate :: a -> a
    negate x = zero - x

class MultiplicativeSemigroup a where
    (*) :: a -> a -> a

class MultiplicativeSemigroup a => MultiplicativeMonoid a where
    one :: a

class MultiplicativeMonoid a => MultiplicativeGroup a where
    {-# MINIMAL (invert | (/)) #-}
    (/) :: a -> a -> a
    x / y = x * invert y

    invert :: a -> a
    invert x = one / x

type Semiring a = (AdditiveMonoid a, MultiplicativeMonoid a)

type Ring a = (AdditiveGroup a, MultiplicativeMonoid a)

-- Note: we expect division/inversion to be partial, i.e. throw an error on zero.
type Field a = (AdditiveGroup a, MultiplicativeGroup a)

class (Field a) => FiniteField a where
    order :: Integer

class (MultiplicativeGroup a, FiniteField b) => Exponent a b where
    (^) :: a -> b -> a

--------------------------------------------------------------------------------

instance AdditiveSemigroup Integer where
    (+) = (Haskell.+)

instance AdditiveMonoid Integer where
    zero = 0

instance AdditiveGroup Integer where
    negate = Haskell.negate

instance MultiplicativeSemigroup Integer where
    (*) = (Haskell.*)

instance MultiplicativeMonoid Integer where
    one = 1