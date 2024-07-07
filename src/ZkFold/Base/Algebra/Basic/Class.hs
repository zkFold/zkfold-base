{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Algebra.Basic.Class where

import           Data.Bool                        (bool)
import           Data.Kind                        (Type)
import           GHC.Natural                      (naturalFromInteger)
import           Numeric.Natural                  (Natural)
import           Prelude                          hiding (Num (..), div, divMod, length, mod, negate, product,
                                                   replicate, sum, (/), (^))
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
class MultiplicativeSemigroup b => Exponent a b where
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
class (MultiplicativeSemigroup a, Exponent a Natural) => MultiplicativeMonoid a where
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

multiExp :: (MultiplicativeMonoid a, Exponent a b, Foldable t) => a -> t b -> a
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

instance {-# OVERLAPPABLE #-} (Scale b a, Functor f) => Scale b (f a) where
    scale = fmap . scale

{- | A class of groups in a multiplicative notation.

While exponentiation by an integer is specified in a constraint, a default
implementation is provided as an @'intPow'@ function. You can provide a faster
alternative yourself, but do not forget to check that your implementation
computes the same results on all inputs.
-}
class (MultiplicativeMonoid a, Exponent a Integer) => MultiplicativeGroup a where
    {-# MINIMAL (invert | (/)) #-}

    -- | Division in a group. The following should hold:
    --
    -- [Division] @x / x == one@
    -- [Cancellation] @(y / x) * x == y@
    -- [Agreement] @x / y == x * invert y@
    (/) :: a -> a -> a
    x / y = x * invert y

    -- | Inverse in a group. The following should hold:
    --
    -- [Left inverse] @invert x * x == one@
    -- [Right inverse] @x * invert x == one@
    -- [Agreement] @invert x == one / x@
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
    -- [Agreement] @negate x == zero - x@
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

{- | A Euclidean domain @R@ is an integral domain which can be endowed
with at least one function @f : R\{0} -> R+@ s.t.
If @a@ and @b@ are in @R@ and @b@ is nonzero, then there exist @q@ and @r@ in @R@ such that
@a = bq + r@ and either @r = 0@ or @f(r) < f(b)@.

@q@ and @r@ are called respectively a quotient and a remainder of the division (or Euclidean division) of @a@ by @b@.

The function @divMod@ associated with this class produces @q@ and @r@ given @a@ and @b@.
-}
class Semiring a => EuclideanDomain a where
    {-# MINIMAL divMod #-}

    divMod :: a -> a -> (a, a)

    div :: a -> a -> a
    div n d = Haskell.fst $ divMod n d

    mod :: a -> a -> a
    mod n d = Haskell.snd $ divMod n d


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

{- | Class of fields. As a ring, each field is commutative, that is:

[Commutativity] @x * y == y * x@

While exponentiation by an integer is specified in a constraint, a default
implementation is provided as an @'intPowF'@ function. You can provide a faster
alternative yourself, but do not forget to check that your implementation
computes the same results on all inputs.
-}
class (Ring a, Exponent a Integer) => Field a where
    {-# MINIMAL (finv | (//)) #-}

    -- | Division in a field. The following should hold:
    --
    -- [Division] If @x /= 0@, @x // x == one@
    -- [Div by 0] @x // zero == zero@
    -- [Agreement] @x // y == x * finv y@
    (//) :: a -> a -> a
    x // y = x * finv y

    -- | Inverse in a field. The following should hold:
    --
    -- [Inverse] If @x /= 0@, @x * inverse x == one@
    -- [Inv of 0] @inverse zero == zero@
    -- [Agreement] @finv x == one // x@
    finv :: a -> a
    finv x = one // x

    -- | @rootOfUnity n@ is an element of a characteristic @2^n@, that is,
    --
    -- [Root of 0] @rootOfUnity 0 == Just one@
    -- [Root property] If @rootOfUnity n == Just x@, @x ^ (2 ^ n) == one@
    -- [Smallest root] If @rootOfUnity n == Just x@ and @m < n@, @x ^ (2 ^ m) /= one@
    -- [All roots] If @rootOfUnity n == Just x@ and @m < n@, @rootOfUnity m /= Nothing@
    rootOfUnity :: Natural -> Maybe a
    rootOfUnity 0 = Just one
    rootOfUnity _ = Nothing

intPowF :: Field a => a -> Integer -> a
-- | A default implementation for integer exponentiation. Uses only natural
-- exponentiation and @'finv'@ so doesn't loop via an @'Exponent' Integer a@
-- instance.
intPowF a n | n < 0     = finv a ^ naturalFromInteger (-n)
            | otherwise = a ^ naturalFromInteger n

{- | Class of finite structures. @Order a@ should be the actual number of
elements in the type, identified up to the associated equality relation.
-}
class (KnownNat (Order a), KnownNat (NumberOfBits a)) => Finite (a :: Type) where
    type Order a :: Natural

order :: forall a . Finite a => Natural
order = value @(Order a)

type NumberOfBits a = Log2 (Order a - 1) + 1

numberOfBits :: forall a . KnownNat (NumberOfBits a) => Natural
numberOfBits = value @(NumberOfBits a)

type FiniteAdditiveGroup a = (Finite a, AdditiveGroup a)

type FiniteMultiplicativeGroup a = (Finite a, MultiplicativeGroup a)

type FiniteField a = (Finite a, Field a)

type PrimeField a = (FiniteField a, Prime (Order a))

{- | A field is a commutative ring in which an element is
invertible if and only if it is nonzero.
In a discrete field an element is invertible xor it equals zero.
That is equivalent in classical logic but stronger in constructive logic.
Every element is either 0 or invertible, and 0 ≠ 1.

We represent a discrete field as a field with an
internal equality function which returns `one`
for equal field elements and `zero` for distinct field elements.
-}
class Field a => DiscreteField' a where
    equal :: a -> a -> a
    default equal :: Eq a => a -> a -> a
    equal a b = bool zero one (a == b)

{- | An ordering of a field is usually required to have compatibility laws with
respect to addition and multiplication. However, we can drop that requirement and
define a trichotomy field as one with an internal total ordering.
We represent a trichotomy field as a discrete field with an internal comparison of
field elements returning `negate` `one` for <, `zero` for =, and `one`
for >. The law of trichotomy is that for any two field elements, exactly one
of the relations <, =, or > holds. Thus we require that -1, 0 and 1 are distinct
field elements.

prop> equal a b = one - (trichotomy a b)^2
-}
class DiscreteField' a => TrichotomyField a where
    trichotomy :: a -> a -> a
    default trichotomy :: Ord a => a -> a -> a
    trichotomy a b = case compare a b of
        LT -> negate one
        EQ -> zero
        GT -> one

--------------------------------------------------------------------------------

{- | Class of semirings where a binary expansion of elements can be computed.
The methods store binary expansion of @a@ as objects of type @b@.
Note: numbers should convert to Little-endian bit representation.

The following should hold:

* @fromBinary . binaryExpansion == id@
* @fromBinary xs == foldr (\x y -> x + y + y) zero xs@
-}
class Semiring a => BinaryExpansion a where
    type Bits a :: Type

    binaryExpansion :: a -> Bits a

    fromBinary :: Bits a -> a
    default fromBinary :: Bits a ~ [a] => Bits a -> a
    fromBinary = foldr (\x y -> x + y + y) zero

padBits :: forall a . AdditiveMonoid a => Natural -> [a] -> [a]
padBits n xs = xs ++ replicate (n -! length xs) zero

castBits :: (Semiring a, Eq a, Semiring b) => [a] -> [b]
castBits []     = []
castBits (x:xs)
    | x == zero = zero : castBits xs
    | x == one  = one  : castBits xs
    | otherwise = error "castBits: impossible bit value"

--------------------------------------------------------------------------------

-- | A multiplicative subgroup of nonzero elements of a field.
-- TODO: hide constructor
newtype NonZero a = NonZero a
    deriving newtype (MultiplicativeSemigroup, MultiplicativeMonoid)

instance Exponent a b => Exponent (NonZero a) b where
    NonZero a ^ b = NonZero (a ^ b)

instance Field a => MultiplicativeGroup (NonZero a) where
    invert (NonZero x) = NonZero (finv x)
    NonZero x / NonZero y = NonZero (x // y)

instance (KnownNat (Order (NonZero a)), KnownNat (NumberOfBits (NonZero a)))
    => Finite (NonZero a) where
    type Order (NonZero a) = Order a - 1

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

instance EuclideanDomain Natural where
    divMod = Haskell.divMod

instance BinaryExpansion Natural where
    type Bits Natural = [Natural]
    binaryExpansion 0 = []
    binaryExpansion x = (x `mod` 2) : binaryExpansion (x `div` 2)

(-!) :: Natural -> Natural -> Natural
(-!) = (Haskell.-)

--------------------------------------------------------------------------------

instance MultiplicativeSemigroup Integer where
    (*) = (Haskell.*)

instance Exponent Integer Natural where
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

instance EuclideanDomain Integer where
    divMod = Haskell.divMod

instance Ring Integer

--------------------------------------------------------------------------------

instance MultiplicativeSemigroup Bool where
    (*) = (&&)

instance (Semiring a, Eq a) => Exponent Bool a where
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
    type Bits Bool = [Bool]

    binaryExpansion = (:[])

    fromBinary []  = False
    fromBinary [x] = x
    fromBinary _   = error "fromBits: This should never happen."

instance MultiplicativeMonoid a => Exponent a Bool where
    _ ^ False = one
    x ^ True  = x

--------------------------------------------------------------------------------

instance MultiplicativeSemigroup a => MultiplicativeSemigroup [a] where
    (*) = zipWith (*)

instance Exponent a b => Exponent [a] b where
    x ^ p = map (^ p) x

instance MultiplicativeMonoid a => MultiplicativeMonoid [a] where
    one = repeat one

instance MultiplicativeGroup a => MultiplicativeGroup [a] where
    invert = map invert

instance AdditiveSemigroup a => AdditiveSemigroup [a] where
    (+) = zipWith (+)

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

instance Exponent a b => Exponent (p -> a) b where
    f ^ p = \x -> f x ^ p

instance MultiplicativeMonoid a => MultiplicativeMonoid (p -> a) where
    one = const one

instance MultiplicativeGroup a => MultiplicativeGroup (p -> a) where
    invert = fmap invert

instance AdditiveSemigroup a => AdditiveSemigroup (p -> a) where
    p1 + p2 = \x -> p1 x + p2 x

instance AdditiveMonoid a => AdditiveMonoid (p -> a) where
    zero = const zero

instance AdditiveGroup a => AdditiveGroup (p -> a) where
    negate = fmap negate

instance FromConstant b a => FromConstant b (p -> a) where
    fromConstant = const . fromConstant

instance Semiring a => Semiring (p -> a)

instance Ring a => Ring (p -> a)
