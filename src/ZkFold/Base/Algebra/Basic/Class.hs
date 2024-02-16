{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Base.Algebra.Basic.Class where

import           Data.Bifunctor (first)
import           Data.Bool      (bool)
import           Prelude        hiding (Num(..), length, negate, product, replicate, sum, (/), (^))
import qualified Prelude        as Haskell
import           System.Random  (RandomGen, Random (..), mkStdGen)

import           ZkFold.Prelude (replicate, length)

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

product1 :: (Foldable t, MultiplicativeSemigroup a) => t a -> a
product1 = foldl1 (*)

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

numberOfBits :: forall a . Finite a => Integer
numberOfBits = ceiling $ logBase @Double 2 $ Haskell.fromInteger $ order @a

class Finite a => Prime a

type FiniteAdditiveGroup a = (Finite a, AdditiveGroup a)

type FiniteMultiplicativeGroup a = (Finite a, MultiplicativeGroup a)

type FiniteField a = (Finite a, Field a)

type PrimeField a = (Prime a, FiniteField a)

--------------------------------------------------------------------------------

class FromConstant a b where
    fromConstant :: a -> b

instance FromConstant a a where
    fromConstant = id

-- Note: numbers should convert to Little-endian bit representation.
class Semiring a => BinaryExpansion a where
    binaryExpansion :: a -> [a]

    fromBinary :: [a] -> a
    fromBinary = foldr (\x y -> x + y + y) zero

padBits :: forall a . BinaryExpansion a => Integer -> [a] -> [a]
padBits n xs = xs ++ replicate (n - length xs) zero

castBits :: (Semiring a, Eq a, Semiring b) => [a] -> [b]
castBits []     = []
castBits (x:xs)
    | x == zero = zero : castBits xs
    | x == one  = one  : castBits xs
    | otherwise = error "castBits: impossible bit value"

class (AdditiveMonoid a, Semiring b) => Scale a b | a -> b where
    scale :: b -> a -> a

type Algebra a b = (Ring a, Scale a b)

class (MultiplicativeMonoid a, Semiring b) => Exponent a b where
    (^) :: a -> b -> a

instance (MultiplicativeMonoid a, Eq b, BinaryExpansion b) => Exponent a b where
    a ^ n = product $ zipWith f (binaryExpansion n) (iterate (\x -> x * x) a)
      where
        f x y
          | x == zero = one
          | x == one  = y
          | otherwise = error "^: This should never happen."

multiExp :: (Exponent a b, Foldable t) => a -> t b -> a
multiExp a = foldl (\x y -> x * (a ^ y)) one

------------------------------- Roots of unity ---------------------------------

-- | Returns a primitive root of unity of order 2^l.
rootOfUnity :: forall a . (PrimeField a, Eq a, FromConstant Integer a) => Integer -> a
rootOfUnity l
    | l <= 0                      = error "rootOfUnity: l should be positive!"
    | (order @a - 1) `mod` n /= 0 = error $ "rootOfUnity: 2^" ++ show l ++ " should divide (p-1)!"
    | otherwise = rootOfUnity' (mkStdGen 0)
    where
        n = 2 ^ l
        rootOfUnity' :: RandomGen g => g -> a
        rootOfUnity' g =
            let (x, g') = first fromConstant $ randomR (1, order @a - 1) g
                x' = x ^ ((order @a - 1) `div` n)
            in bool (rootOfUnity' g') x' (x' ^ (n `div` 2) /= one)

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

instance BinaryExpansion Integer where
    binaryExpansion 0 = []
    binaryExpansion x
        | x > 0     = (x `mod` 2) : binaryExpansion (x `div` 2)
        | otherwise = error "toBits: Not defined for negative integers!"

--------------------------------------------------------------------------------

instance AdditiveSemigroup Bool where
    (+) = (||)

instance AdditiveMonoid Bool where
    zero = False

instance AdditiveGroup Bool where
    negate = id

instance MultiplicativeSemigroup Bool where
    (*) = (&&)

instance MultiplicativeMonoid Bool where
    one = True

instance MultiplicativeGroup Bool where
    invert = id

instance ToBits Bool where
    toBits = (:[])

instance FromBits Bool where
    fromBits []  = False
    fromBits [x] = x
    fromBits _   = error "fromBits: This should never happen."

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
