{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module ZkFold.Base.Algebra.Basic.Class where

import           Data.Kind                        (Type)
import           GHC.Natural                      (naturalFromInteger)
import           Numeric.Natural                  (Natural)
import           Prelude                          hiding (Num (..), length, negate, product, replicate, sum, (/), (^))
import qualified Prelude                          as Haskell

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Prelude                   (length, replicate)

infixl 7 *, /
infixl 6 +, -, -!

class FromConstant a b where
    fromConstant :: a -> b

instance FromConstant a a where
    fromConstant = id

class ToConstant a b where
    toConstant :: a -> b

instance ToConstant a a where
    toConstant = id

--------------------------------------------------------------------------------

class MultiplicativeSemigroup a where
    (*) :: a -> a -> a

product1 :: (Foldable t, MultiplicativeSemigroup a) => t a -> a
product1 = foldl1 (*)

class MultiplicativeSemigroup b => Exponent b a where
    (^) :: a -> b -> a

class (MultiplicativeSemigroup a, Exponent Natural a) => MultiplicativeMonoid a where
    one :: a

natPow :: MultiplicativeMonoid a => a -> Natural -> a
natPow a n = product $ zipWith f (binaryExpansion n) (iterate (\x -> x * x) a)
  where
    f 0 _ = one
    f 1 x = x
    f _ _ = error "^: This should never happen."

product :: (Foldable t, MultiplicativeMonoid a) => t a -> a
product = foldl (*) one

multiExp :: (MultiplicativeMonoid a, Exponent b a, Foldable t) => a -> t b -> a
multiExp a = foldl (\x y -> x * (a ^ y)) one

class MultiplicativeMonoid b => Scale b a where
    scale :: b -> a -> a
    default scale :: (FromConstant b a, MultiplicativeSemigroup a) => b -> a -> a
    scale = (*) . fromConstant

instance MultiplicativeMonoid a => Scale a a

class (MultiplicativeMonoid a, Exponent Integer a) => MultiplicativeGroup a where
    {-# MINIMAL (invert | (/)) #-}
    (/) :: a -> a -> a
    x / y = x * invert y

    invert :: a -> a
    invert x = one / x

intPow :: MultiplicativeGroup a => a -> Integer -> a
intPow a n | n < 0     = invert a ^ naturalFromInteger (-n)
           | otherwise = a ^ naturalFromInteger n

--------------------------------------------------------------------------------

class AdditiveSemigroup a where
    (+) :: a -> a -> a

class (AdditiveSemigroup a, Scale Natural a) => AdditiveMonoid a where
    zero :: a

natScale :: AdditiveMonoid a => Natural -> a -> a
natScale n a = sum $ zipWith f (binaryExpansion n) (iterate (\x -> x + x) a)
  where
    f 0 _ = zero
    f 1 x = x
    f _ _ = error "scale: This should never happen."

sum :: (Foldable t, AdditiveMonoid a) => t a -> a
sum = foldl (+) zero

class (AdditiveMonoid a, Scale Integer a) => AdditiveGroup a where
    {-# MINIMAL (negate | (-)) #-}
    (-) :: a -> a -> a
    x - y = x + negate y

    negate :: a -> a
    negate x = zero - x

intScale :: AdditiveGroup a => Integer -> a -> a
intScale n a | n < 0     = naturalFromInteger (-n) `scale` negate a
             | otherwise = naturalFromInteger n `scale` a

--------------------------------------------------------------------------------

class (AdditiveMonoid a, MultiplicativeMonoid a, FromConstant Natural a) => Semiring a

class (Semiring a, AdditiveGroup a, FromConstant Integer a) => Ring a

type Algebra b a = (Ring a, Scale b a, FromConstant b a)

-- NOTE: by convention, division by zero returns zero.
class (Ring a, MultiplicativeGroup a) => Field a where
    rootOfUnity :: Natural -> Maybe a
    rootOfUnity 0 = Just one
    rootOfUnity _ = Nothing

class KnownNat (Order a) => Finite (a :: Type) where
    type Order a :: Natural

order :: forall a . Finite a => Natural
order = value @(Order a)

numberOfBits :: forall a . Finite a => Natural
numberOfBits = ceiling $ logBase @Double 2 $ Haskell.fromIntegral $ order @a

type FiniteAdditiveGroup a = (Finite a, AdditiveGroup a)

type FiniteMultiplicativeGroup a = (Finite a, MultiplicativeGroup a)

type FiniteField a = (Finite a, Field a)

type PrimeField a = (FiniteField a, Prime (Order a))

--------------------------------------------------------------------------------

-- Note: numbers should convert to Little-endian bit representation.
class Semiring a => BinaryExpansion a where
    binaryExpansion :: a -> [a]

    fromBinary :: [a] -> a
    fromBinary = foldr (\x y -> x + y + y) zero

padBits :: forall a . BinaryExpansion a => Natural -> [a] -> [a]
padBits n xs = xs ++ replicate (n -! length xs) zero

castBits :: (Semiring a, Eq a, Semiring b) => [a] -> [b]
castBits []     = []
castBits (x:xs)
    | x == zero = zero : castBits xs
    | x == one  = one  : castBits xs
    | otherwise = error "castBits: impossible bit value"

--------------------------------------------------------------------------------

instance MultiplicativeSemigroup Natural where
    (*) = (Haskell.*)

instance Exponent Natural Natural where
    (^) = (Haskell.^)

instance MultiplicativeMonoid Natural where
    one = 1

instance AdditiveSemigroup Natural where
    (+) = (Haskell.+)

instance AdditiveMonoid Natural where
    zero = 0

instance Semiring Natural

instance BinaryExpansion Natural where
    binaryExpansion 0 = []
    binaryExpansion x = (x `mod` 2) : binaryExpansion (x `div` 2)

(-!) :: Natural -> Natural -> Natural
(-!) = (Haskell.-)

--------------------------------------------------------------------------------

instance MultiplicativeSemigroup Integer where
    (*) = (Haskell.*)

instance Exponent Natural Integer where
    (^) = (Haskell.^)

instance MultiplicativeMonoid Integer where
    one = 1

instance AdditiveSemigroup Integer where
    (+) = (Haskell.+)

instance Scale Natural Integer

instance AdditiveMonoid Integer where
    zero = 0

instance AdditiveGroup Integer where
    negate = Haskell.negate

instance FromConstant Natural Integer where
    fromConstant = Haskell.fromIntegral

instance Semiring Integer

instance Ring Integer

--------------------------------------------------------------------------------

instance MultiplicativeSemigroup Bool where
    (*) = (&&)

instance (Semiring a, Eq a) => Exponent a Bool where
    x ^ p | p == zero = one
          | otherwise = x

instance MultiplicativeMonoid Bool where
    one = True

instance MultiplicativeGroup Bool where
    invert = id

instance AdditiveSemigroup Bool where
    (+) = (/=)

instance Scale Natural Bool

instance AdditiveMonoid Bool where
    zero = False

instance Scale Integer Bool

instance AdditiveGroup Bool where
    negate = id

instance FromConstant Natural Bool where
    fromConstant = odd

instance Semiring Bool

instance FromConstant Integer Bool where
    fromConstant = odd

instance Ring Bool

instance BinaryExpansion Bool where
    binaryExpansion = (:[])

    fromBinary []  = False
    fromBinary [x] = x
    fromBinary _   = error "fromBits: This should never happen."

instance MultiplicativeMonoid a => Exponent Bool a where
    _ ^ False = one
    x ^ True  = x

--------------------------------------------------------------------------------

instance MultiplicativeSemigroup a => MultiplicativeSemigroup [a] where
    (*) = zipWith (*)

instance Exponent b a => Exponent b [a] where
    x ^ p = map (^ p) x

instance MultiplicativeMonoid a => MultiplicativeMonoid [a] where
    one = repeat one

instance MultiplicativeGroup a => MultiplicativeGroup [a] where
    invert = map invert

instance AdditiveSemigroup a => AdditiveSemigroup [a] where
    (+) = zipWith (+)

instance Scale b a => Scale b [a] where
    scale = map . scale

instance AdditiveMonoid a => AdditiveMonoid [a] where
    zero = repeat zero

instance AdditiveGroup a => AdditiveGroup [a] where
    negate = map negate

instance FromConstant b a => FromConstant b [a] where
    fromConstant = repeat . fromConstant

instance Semiring a => Semiring [a]

instance Ring a => Ring [a]

--------------------------------------------------------------------------------

instance MultiplicativeSemigroup a => MultiplicativeSemigroup (p -> a) where
    p1 * p2 = \x -> p1 x * p2 x

instance Exponent b a => Exponent b (p -> a) where
    f ^ p = \x -> f x ^ p

instance MultiplicativeMonoid a => MultiplicativeMonoid (p -> a) where
    one = const one

instance MultiplicativeGroup a => MultiplicativeGroup (p -> a) where
    invert = fmap invert

instance AdditiveSemigroup a => AdditiveSemigroup (p -> a) where
    p1 + p2 = \x -> p1 x + p2 x

instance Scale b a => Scale b (p -> a) where
    scale c p = scale c . p

instance AdditiveMonoid a => AdditiveMonoid (p -> a) where
    zero = const zero

instance AdditiveGroup a => AdditiveGroup (p -> a) where
    negate = fmap negate

instance FromConstant b a => FromConstant b (p -> a) where
    fromConstant = const . fromConstant

instance Semiring a => Semiring (p -> a)

instance Ring a => Ring (p -> a)
