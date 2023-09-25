{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Crypto.Algebra.Basic.Class where

import           Prelude hiding (Num(..), (^), (/), negate)
import qualified Prelude as Haskell

infixl 7 *, /
infixl 6 +, -

class AdditiveSemigroup a where
    (+) :: a -> a -> a

class AdditiveSemigroup a => AdditiveMonoid a where
    zero :: a

sum :: (Foldable t, AdditiveMonoid a) => t a -> a
sum = foldl (+) zero

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

product :: (Foldable t, MultiplicativeMonoid a) => t a -> a
product = foldl (*) one

class MultiplicativeMonoid a => MultiplicativeGroup a where
    {-# MINIMAL (invert | (/)) #-}
    (/) :: a -> a -> a
    x / y = x * invert y

    invert :: a -> a
    invert x = one / x

type Semiring a = (AdditiveMonoid a, MultiplicativeMonoid a)

type Ring a = (AdditiveGroup a, MultiplicativeMonoid a)

-- NOTE: by convention, division by zero returns zero.
type Field a = (AdditiveGroup a, MultiplicativeGroup a)

class Finite a where
    order :: Integer

class Finite a => Prime a

type FiniteAdditiveGroup a = (Finite a, AdditiveGroup a)

type FiniteMultiplicativeGroup a = (Finite a, MultiplicativeGroup a)

type FiniteField a = (Finite a, Field a)

type PrimeField a = (Prime a, FiniteField a)

--------------------------------------------------------------------------------

class FromConstant a b where
    fromConstant :: a -> b

-- Note: numbers should convert to Little-endian bit representation.
class Semiring a => ToBits a where
    toBits :: a -> [a]

class MultiplicativeSemigroup a => Exponent a b where
    (^) :: a -> b -> a

instance (MultiplicativeMonoid a, Semiring b, Eq b, ToBits b) => Exponent a b where
    a ^ n = foldl (*) one $ zipWith f (toBits n) (iterate (\x -> x * x) a)
      where
        f x y
            | x == zero = one
            | x == one  = y
            | otherwise = error "^: This should never happen."

multiExp :: (MultiplicativeMonoid a, Exponent a b, Foldable t) => a -> t b -> a
multiExp a = foldl (\x y -> x * (a ^ y)) one

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

instance ToBits Integer where
    toBits 0 = []
    toBits x
        | x > 0     = (x `mod` 2) : toBits (x `div` 2)
        | otherwise = error "toBits: Not defined for negative integers!"

--------------------------------------------------------------------------------

instance AdditiveSemigroup a => AdditiveSemigroup [a] where
    (+) = zipWith (+)

instance AdditiveMonoid a => AdditiveMonoid [a] where
    zero = repeat zero

instance AdditiveGroup a => AdditiveGroup [a] where
    negate = map negate

instance MultiplicativeSemigroup a => MultiplicativeSemigroup [a] where
    (*) = zipWith (*)

instance MultiplicativeMonoid a => MultiplicativeMonoid [a] where
    one = repeat one

instance MultiplicativeGroup a => MultiplicativeGroup [a] where
    invert = map invert

--------------------------------------------------------------------------------

instance AdditiveSemigroup a => AdditiveSemigroup (p -> a) where
    p1 + p2 = \x -> p1 x + p2 x

instance AdditiveMonoid a => AdditiveMonoid (p -> a) where
    zero = const zero

instance AdditiveGroup a => AdditiveGroup (p -> a) where
    negate = fmap negate

instance MultiplicativeSemigroup a => MultiplicativeSemigroup (p -> a) where
    p1 * p2 = \x -> p1 x * p2 x

instance MultiplicativeMonoid a => MultiplicativeMonoid (p -> a) where
    one = const one

instance MultiplicativeGroup a => MultiplicativeGroup (p -> a) where
    invert = fmap invert