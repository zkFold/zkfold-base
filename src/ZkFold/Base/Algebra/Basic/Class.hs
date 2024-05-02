{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Algebra.Basic.Class where

import           Control.Arrow                    ((***))
import           Control.Monad.State              (runState, state)
import           Data.Bool                        (bool)
import           Data.Distributive
import           Data.Functor.Identity            (Identity (..))
import           Data.Functor.Rep
import           Data.Kind                        (Type)
import           Data.Void                        (Void, absurd)
import           GHC.Generics                     (U1 (..), (:*:) (..), (:.:) (..))
import           GHC.Natural                      (naturalFromInteger)
import           Numeric.Natural                  (Natural)
import           Prelude                          hiding (Num (..), length, negate, product, replicate, sum, (/), (^))
import qualified Prelude                          as Haskell
import           System.Random                    (Random (..))
import           Test.QuickCheck                  (Arbitrary (..))

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

class Field a => DiscreteField' a where
    equal :: a -> a -> a
    default equal :: Eq a => a -> a -> a
    equal a b = bool zero one (a == b)

class DiscreteField' a => Trichotomy a where
    trichotomy :: a -> a -> a
    default trichotomy :: Ord a => a -> a -> a
    trichotomy a b = case compare a b of
        LT -> negate one
        EQ -> zero
        GT -> one

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

instance BinaryExpansion Natural where
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

--------------------------------------------------------------------------------

{- | Class of vector spaces with a basis over a field. -}
class
  ( Field a
  , AdditiveGroup (v a)
  , Scale a (v a)
  ) => VectorSpace a v where
    type Basis a v :: Type
    tabulateV :: (Basis a v -> a) -> v a
    indexV :: v a -> Basis a v -> a

-- basis vector e_i
basisV :: (VectorSpace a v, Eq (Basis a v)) => Basis a v -> v a
basisV i = tabulateV $ \j -> if i == j then one else zero

-- dot product
-- prop> v `dotV` basis i = indexV v i
dotV :: (VectorSpace a v, Foldable v) => v a -> v a -> a
v `dotV` w = sum (zipWithV (*) v w)

zipWithV :: VectorSpace a v => (a -> a -> a) -> v a -> v a -> v a
zipWithV f as bs = tabulateV $ \k ->
  f (indexV as k) (indexV bs k)

mapV :: VectorSpace a v => (a -> a) -> v a -> v a
mapV f = tabulateV . fmap f . indexV

pureV :: VectorSpace a v => a -> v a
pureV = tabulateV . const

{- | `Tensorial` class of multilinear functions.

The type @Tensorial a t => t@ should be equivalent to

@(VectorSpace a v0, .. ,VectorSpace a vN) => vN a -> .. -> v0 a@

`Tensorial` builds contravariant tensor indices with (->).
To build covariant indices use the tensor product `(:.:)`.
-}
class (Field a, VectorSpace a (OutputSpace a t)) => Tensorial a t where
  indexT :: t -> (InputBasis a t -> a) -> OutputSpace a t a
  tabulateT :: ((InputBasis a t -> a) -> OutputSpace a t a) -> t

-- | The type of lower indices of a tensor
type family InputBasis a t where
  InputBasis a (x a -> t) = Either (Basis a x) (InputBasis a t)
  InputBasis a (y a) = Void

type family OutputSpace a t where
  OutputSpace a (x a -> t) = OutputSpace a t
  OutputSpace a (y a) = y

instance {-# OVERLAPPABLE #-}
  ( VectorSpace a y
  , OutputSpace a (y a) ~ y
  , InputBasis a (y a) ~ Void
  ) => Tensorial a (y a) where
    indexT t _ = t
    tabulateT f = f absurd

instance {-# OVERLAPPING #-}
  ( VectorSpace a x
  , OutputSpace a (x a -> t) ~ OutputSpace a t
  , InputBasis a (x a -> t) ~ Either (Basis a x) (InputBasis a t)
  , Tensorial a t
  ) => Tensorial a (x a -> t) where
    indexT t i = indexT (t (tabulateV (i . Left))) (i . Right)
    tabulateT f x = tabulateT (f . either (indexV x))

-- representable vector space
newtype Representably v (a :: Type) = Representably
  { runRepresentably :: v a }
instance (Field a, Representable v)
  => VectorSpace a (Representably v) where
    type Basis a (Representably v) = Rep v
    tabulateV = Representably . tabulate
    indexV = index . runRepresentably
instance (Representable v, AdditiveSemigroup a)
  => AdditiveSemigroup (Representably v a) where
    Representably a + Representably b =
        Representably (mzipWithRep (+) a b)
instance (Representable v, AdditiveMonoid a)
  => AdditiveMonoid (Representably v a) where
    zero = Representably (pureRep zero)
instance (Representable v, AdditiveGroup a)
  => AdditiveGroup (Representably v a) where
    Representably a - Representably b =
        Representably (mzipWithRep (-) a b)
instance (Representable v, Scale b a)
  => Scale b (Representably v a) where
    scale b (Representably v) = Representably (fmapRep (scale b) v)

instance Representable v => Distributive (Representably v) where
  distribute = Representably . distribute . fmap runRepresentably
  collect f = Representably . (collect (runRepresentably . f))

instance Representable v => Functor (Representably v) where
  fmap f = Representably . fmapRep f . runRepresentably

instance Representable v => Applicative (Representably v) where
  pure = Representably . pureRep
  Representably f <*> Representably a = Representably (f `apRep` a)

deriving newtype instance Foldable v => Foldable (Representably v)

instance (Traversable v, Representable v) => Traversable (Representably v) where
    traverse f (Representably v) = fmap Representably (traverse f v)

instance (Representable v, Traversable v, Random a) => Random (Representably v a) where
  random = runState (sequenceA (Representably (pureRep (state random))))
  randomR
    = runState
    . fmap Representably
    . sequenceA
    . fmapRep (state . randomR)
    . uncurry mzipRep
    . (runRepresentably *** runRepresentably)

instance (Arbitrary a, Representable v, Traversable v)
  => Arbitrary (Representably v a) where
    arbitrary = sequenceA (Representably (pureRep arbitrary))

-- Linearly via vector space
newtype Linearly v (a :: Type) = Linearly
  { runLinearly :: v a }
instance VectorSpace a v
  => AdditiveSemigroup (Linearly v a) where
    Linearly a + Linearly b =
        Linearly (zipWithV (+) a b)
instance VectorSpace a v
  => AdditiveMonoid (Linearly v a) where
    zero = Linearly (pureV zero)
instance VectorSpace a v
  => AdditiveGroup (Linearly v a) where
    Linearly a - Linearly b =
        Linearly (zipWithV (-) a b)
instance (Scale b a, VectorSpace a v)
  => Scale b (Linearly v a) where
    scale b (Linearly v) = Linearly (mapV (scale b) v)

-- zero dimensional vector space
deriving via Representably U1 instance Field a => VectorSpace a U1
deriving via Representably U1 a instance Field a => AdditiveSemigroup (U1 a)
deriving via Representably U1 a instance Field a => AdditiveMonoid (U1 a)
deriving via Representably U1 a instance Field a => AdditiveGroup (U1 a)
deriving via Representably U1 a instance Field a => Scale Natural (U1 a)
deriving via Representably U1 a instance Field a => Scale Integer (U1 a)
deriving via Representably U1 a instance Field a => Scale a (U1 a)

-- one dimensional vector space
deriving newtype instance FromConstant Natural a => FromConstant Natural (Identity a)
deriving newtype instance FromConstant Integer a => FromConstant Integer (Identity a)
deriving via Representably Identity instance Field a => VectorSpace a Identity
deriving via Representably Identity a instance Field a => AdditiveSemigroup (Identity a)
deriving via Representably Identity a instance Field a => AdditiveMonoid (Identity a)
deriving via Representably Identity a instance Field a => AdditiveGroup (Identity a)
deriving via Representably Identity a instance Field a => Scale Natural (Identity a)
deriving via Representably Identity a instance Field a => Scale Integer (Identity a)
deriving via Representably Identity a instance Field a => Scale a (Identity a)

-- direct sum of vector spaces
instance (VectorSpace a v, VectorSpace a u)
  => VectorSpace a (v :*: u) where
    type Basis a (v :*: u) = Either (Basis a v) (Basis a u)
    tabulateV f = tabulateV (f . Left) :*: tabulateV (f . Right)
    indexV (a :*: _) (Left  i) = indexV a i
    indexV (_ :*: b) (Right j) = indexV b j
instance (VectorSpace a v, VectorSpace a u)
  => AdditiveSemigroup ((v :*: u) a) where
    (a0 :*: a1) + (b0 :*: b1) = (a0 + b0) :*: (a1 + b1)
instance (VectorSpace a v, VectorSpace a u)
  => AdditiveMonoid ((v :*: u) a) where
    zero = zero :*: zero
instance (VectorSpace a v, VectorSpace a u)
  => AdditiveGroup ((v :*: u) a) where
    (a0 :*: a1) - (b0 :*: b1) = (a0 - b0) :*: (a1 - b1)
instance (VectorSpace a v, VectorSpace a u)
  => Scale Natural ((v :*: u) a) where
    scale n (a0 :*: a1) = (scale n a0) :*: (scale n a1)
instance (VectorSpace a v, VectorSpace a u)
  => Scale Integer ((v :*: u) a) where
    scale n (a0 :*: a1) = (scale n a0) :*: (scale n a1)
instance (VectorSpace a v, VectorSpace a u)
  => Scale a ((v :*: u) a) where
    scale n (a0 :*: a1) = (scale n a0) :*: (scale n a1)

-- tensor product of vector spaces
instance (Representable u, VectorSpace a v)
  => VectorSpace a (u :.: v) where
    type Basis a (u :.: v) = (Rep u, Basis a v)
    tabulateV = Comp1 . tabulate . fmap tabulateV . curry
    indexV (Comp1 fg) (i, j) = indexV (index fg i) j
instance (Representable u, VectorSpace a v)
  => AdditiveSemigroup ((u :.: v) a) where
    Comp1 a + Comp1 b = Comp1 (mzipWithRep (zipWithV (+)) a b)
instance (Representable u, VectorSpace a v)
  => AdditiveMonoid ((u :.: v) a) where
    zero = Comp1 (pureRep (pureV zero))
instance (Representable u, VectorSpace a v)
  => AdditiveGroup ((u :.: v) a) where
    Comp1 a - Comp1 b = Comp1 (mzipWithRep (zipWithV (-)) a b)
instance (Functor u, VectorSpace a v)
  => Scale Natural ((u :.: v) a) where
    scale b (Comp1 a) = Comp1 (fmap (mapV (scale b)) a)
instance (Functor u, VectorSpace a v)
  => Scale Integer ((u :.: v) a) where
    scale b (Comp1 a) = Comp1 (fmap (mapV (scale b)) a)
instance (Functor u, VectorSpace a v)
  => Scale a ((u :.: v) a) where
    scale b (Comp1 a) = Comp1 (fmap (mapV (scale b)) a)
