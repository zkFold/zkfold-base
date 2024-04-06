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

{- | Every algebraic structure has a handful of "constant types" related
with it: natural numbers, integers, field of constants etc. This typeclass
captures this relation.
-}
class FromConstant a b where
    -- | Builds an element of an algebraic structure from a constant.
    --
    -- @fromConstant@ should preserve algebraic structure, e.g. if both the
    -- structure and the type of constants are additive monoids, the following
    -- should hold:
    --
    -- [Homomorphism] @fromConstant (c + d) == fromConstant c + fromConstant d@
    fromConstant :: a -> b

instance FromConstant a a where
    fromConstant = id

class ToConstant a b where
    toConstant :: a -> b

instance ToConstant a a where
    toConstant = id

--------------------------------------------------------------------------------

{- | A class of types with a binary associative operation with a multiplicative
feel to it. Not necessarily commutative.
-}
class MultiplicativeSemigroup a where
    -- | A binary associative operation. The following should hold:
    --
    -- [Associativity] @x * (y * z) == (x * y) * z@
    (*) :: a -> a -> a

product1 :: (Foldable t, MultiplicativeSemigroup a) => t a -> a
product1 = foldl1 (*)

{- | A class for semigroup (and monoid) actions on types where exponential
notation is the most natural (including an exponentiation itself).
-}
class MultiplicativeSemigroup b => Exponent b a where
    -- | A right semigroup action on a type. The following should hold:
    --
    -- [Compatibility] @a ^ (m * n) == (a ^ m) ^ n@
    --
    -- If exponents form a monoid, the following should also hold:
    --
    -- [Right identity] @a ^ one == a@
    --
    -- NOTE, however, that even if exponents form a semigroup, left
    -- distributivity (that @a ^ (m + n) == (a ^ m) * (a ^ n)@) is desirable but
    -- not required: otherwise instance for Bool as exponent could not be made
    -- lawful.
    (^) :: a -> b -> a

{- | A class of types with a binary associative operation with a multiplicative
feel to it and an identity element. Not necessarily commutative.

While exponentiation by a natural is specified as a constraint, a default
implementation is provided as a @'natPow'@ function. You can provide a faster
alternative, but do not forget to check that it satisfies the following
(in addition to the properties already stated in @'Exponent'@ documentation):

[Left identity] @one ^ n == one@
[Absorption] @a ^ 0 == one@
[Left distributivity] @a ^ (m + n) == (a ^ m) * (a ^ n)@

Finally, if the base monoid operation is commutative, power should
distribute over @('*')@:

[Right distributivity] @(a * b) ^ n == (a ^ n) * (b ^ n)@
-}
class (MultiplicativeSemigroup a, Exponent Natural a) => MultiplicativeMonoid a where
    -- | An identity with respect to multiplication:
    --
    -- [Left identity] @one * x == x@
    -- [Right identity] @x * one == x@
    one :: a

natPow :: MultiplicativeMonoid a => a -> Natural -> a
-- | A default implementation for natural exponentiation. Uses only @('*')@ and
-- @'one'@ so doesn't loop via an @'Exponent' Natural a@ instance.
natPow a n = product $ zipWith f (binaryExpansion n) (iterate (\x -> x * x) a)
  where
    f 0 _ = one
    f 1 x = x
    f _ _ = error "^: This should never happen."

product :: (Foldable t, MultiplicativeMonoid a) => t a -> a
product = foldl (*) one

multiExp :: (MultiplicativeMonoid a, Exponent b a, Foldable t) => a -> t b -> a
multiExp a = foldl (\x y -> x * (a ^ y)) one

{- | A class for monoid actions where multiplicative notation is the most
natural (including multiplication by constant itself).
-}
class MultiplicativeMonoid b => Scale b a where
    -- | A left monoid action on a type. Should satisfy the following:
    --
    -- [Compatibility] @scale (c * d) a == scale c (scale d a)@
    -- [Left identity] @scale one a == a@
    --
    -- If, in addition, a cast from constant is defined, they should agree:
    --
    -- [Scale agrees] @scale c a == fromConstant c * a@
    -- [Cast agrees] @fromConstant c == scale c one@
    --
    -- If the action is on an abelian structure, scaling should respect it:
    --
    -- [Left distributivity] @scale c (a + b) == scale c a + scale c b@
    -- [Right absorption] @scale c zero == zero@
    --
    -- If, in addition, the scaling itself is abelian, this structure should
    -- propagate:
    --
    -- [Right distributivity] @scale (c + d) a == scale c a + scale d a@
    -- [Left absorption] @scale zero a == zero@
    --
    -- The default implementation is the multiplication by a constant.
    scale :: b -> a -> a
    default scale :: (FromConstant b a, MultiplicativeSemigroup a) => b -> a -> a
    scale = (*) . fromConstant

instance MultiplicativeMonoid a => Scale a a

{- | A class of groups in a multiplicative notation.

While exponentiation by an integer is specified in a constraint, a default
implementation is provided as an @'intPow'@ function. You can provide a faster
alternative yourself, but do not forget to check that your implementation
computes the same results on all inputs.
-}
class (MultiplicativeMonoid a, Exponent Integer a) => MultiplicativeGroup a where
    {-# MINIMAL (invert | (/)) #-}

    -- | Division in a group.
    --
    -- If @x@ is invertible, the following should hold:
    --
    -- [Division] @x / x == one@
    -- [Cancellation] @(y / x) * x == y@
    --
    -- In addition, @x / y == x * invert y@ should always hold.
    (/) :: a -> a -> a
    x / y = x * invert y

    -- | Inverse in a group.
    --
    -- If @x@ is invertible, the following should hold:
    --
    -- [Left inverse] @invert x * x == one@
    -- [Right inverse] @x * invert x == one@
    --
    -- In addition, @invert x == one / x@ should always hold.
    invert :: a -> a
    invert x = one / x

intPow :: MultiplicativeGroup a => a -> Integer -> a
-- | A default implementation for integer exponentiation. Uses only natural
-- exponentiation and @'invert'@ so doesn't loop via an @'Exponent' Integer a@
-- instance.
intPow a n | n < 0     = invert a ^ naturalFromInteger (-n)
           | otherwise = a ^ naturalFromInteger n

--------------------------------------------------------------------------------

-- | A class of types with a binary associative, commutative operation.
class AdditiveSemigroup a where
    -- | A binary associative commutative operation. The following should hold:
    --
    -- [Associativity] @x + (y + z) == (x + y) + z@
    -- [Commutativity] @x + y == y + x@
    (+) :: a -> a -> a

{- | A class of types with a binary associative, commutative operation and with
an identity element.

While scaling by a natural is specified as a constraint, a default
implementation is provided as a @'natScale'@ function.
-}
class (AdditiveSemigroup a, Scale Natural a) => AdditiveMonoid a where
    -- | An identity with respect to addition:
    --
    -- [Identity] @x + zero == x@
    zero :: a

natScale :: AdditiveMonoid a => Natural -> a -> a
-- | A default implementation for natural scaling. Uses only @('+')@ and
-- @'zero'@ so doesn't loop via a @'Scale' Natural a@ instance.
natScale n a = sum $ zipWith f (binaryExpansion n) (iterate (\x -> x + x) a)
  where
    f 0 _ = zero
    f 1 x = x
    f _ _ = error "scale: This should never happen."

sum :: (Foldable t, AdditiveMonoid a) => t a -> a
sum = foldl (+) zero

{- | A class of abelian groups.

While scaling by an integer is specified in a constraint, a default
implementation is provided as an @'intScale'@ function.
-}
class (AdditiveMonoid a, Scale Integer a) => AdditiveGroup a where
    {-# MINIMAL (negate | (-)) #-}

    -- | Subtraction in an abelian group. The following should hold:
    --
    -- [Subtraction] @x - x == zero@
    -- [Agreement] @x - y == x + negate y@
    (-) :: a -> a -> a
    x - y = x + negate y

    -- | Inverse in an abelian group. The following should hold:
    --
    -- [Negative] @x + negate x == zero@
    -- [Agreement] @invert x == zero - x@
    negate :: a -> a
    negate x = zero - x

intScale :: AdditiveGroup a => Integer -> a -> a
-- | A default implementation for integer scaling. Uses only natural scaling and
-- @'negate'@ so doesn't loop via a @'Scale' Integer a@ instance.
intScale n a | n < 0     = naturalFromInteger (-n) `scale` negate a
             | otherwise = naturalFromInteger n `scale` a

--------------------------------------------------------------------------------

{- | Class of semirings with both 0 and 1. The following should hold:

[Left distributivity] @a * (b + c) == a * b + a * c@
[Right distributivity] @(a + b) * c == a * c + b * c@
-}
class (AdditiveMonoid a, MultiplicativeMonoid a, FromConstant Natural a) => Semiring a

{- | Class of rings with both 0, 1 and additive inverses. The following should hold:

[Left distributivity] @a * (b - c) == a * b - a * c@
[Right distributivity] @(a - b) * c == a * c - b * c@
-}
class (Semiring a, AdditiveGroup a, FromConstant Integer a) => Ring a

{- | Type of modules/algebras over the base type of constants @b@. As all the
required laws are implied by the constraints, this is simply an alias rather
than a typeclass in its own right.

Note the following useful facts:

* every 'Ring' is an algebra over natural numbers and over integers;
* every 'Ring' is an algebra over itself. However, due to the possible
overlapping instances of @Scale a a@ and @FromConstant a a@ you might
need to defer the resolution of these constraints until @a@ is specified.
-}
type Algebra b a = (Ring a, Scale b a, FromConstant b a)

{- | Class of fields.

NOTE: by convention, division by zero returns zero.
NOTE: every element is either zero or is invertible.

[Division by zero] @x / zero == zero@
[Inverse of zero] @invert zero == zero@
-}
class (Ring a, MultiplicativeGroup a) => Field a where
    rootOfUnity :: Natural -> Maybe a
    rootOfUnity 0 = Just one
    rootOfUnity _ = Nothing

{- | Class of finite structures. @Order a@ should be the actual number of
elements in the type, identified up to the associated equality relation.
-}
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

{- | Class of semirings where a binary expansion of elements can be computed.
Note: numbers should convert to Little-endian bit representation.

The following should hold:

* @fromBinary . binaryExpansion == id@
* @fromBinary xs == foldr (\x y -> x + y + y) zero xs@
-}
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
