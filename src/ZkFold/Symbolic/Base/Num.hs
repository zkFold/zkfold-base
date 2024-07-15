{-# LANGUAGE AllowAmbiguousTypes     #-}
{-# LANGUAGE DerivingStrategies      #-}
{-# LANGUAGE MagicHash               #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module ZkFold.Symbolic.Base.Num
  ( -- * Numeric types
    Integer
  , Natural
  , Rational
  , Int
  , Mod
    -- * Arithmetic constraints
  , Arithmetic
  , PrimeField
    -- * Algebraic constraints
  , AdditiveMonoid (..)
  , MultiplicativeMonoid (..)
  , AdditiveGroup (..)
  , MultiplicativeGroup (..)
  , Semiring
  , Ring
  , Field
  , Algebra
  , SemiEuclidean (..)
  , Euclidean (..)
  , SemiIntegral
  , Integral
  , Modular
  , Discrete (..)
  , Comparable (..)
    -- * Algebraic inter-constraints
  , From (..)
  , Into (..)
  , Exponent (..), (^), (^^)
  , Scalar (..)
    -- * Type level numbers
  , KnownNat
  , Prime
  , Finite (..)
  , FiniteChr (..)
    -- * Numeric combinators
  , sum
  , product
  , even
  , odd
  , fromInteger
  , fromSemiIntegral
  , knownNat
  , order
  , characteristic
  , combineN
  , combineZ
  , evalMonoN
  ) where

import           Control.Applicative
import           Control.Category
import           Data.Bool
import           Data.Eq
import           Data.Foldable       hiding (product, sum, toList)
import           Data.Functor
import           Data.Kind
import           Data.Ord
import           Data.Ratio
import           Data.Type.Bool
import           Data.Type.Equality
import           GHC.Exts            (proxy#)
import           GHC.TypeLits        (ErrorMessage (..), TypeError)
import           GHC.TypeNats        hiding (Mod)
import qualified GHC.TypeNats        as Type
import           Prelude             (Int, Integer)
import qualified Prelude

-- Arithmetic algebras should include:
-- PrimeField x => Arithmetic x x
-- PrimeField x => Arithmetic x (i -> x)
-- PrimeField x => Arithmetic x (Circuit x i Par1)
type Arithmetic x a =
  ( Algebra x a
  , Comparable a
  , FiniteChr a
  , 3 <= Chr a
  )

-- Prime fields should only include:
-- (SemiIntegral int, Prime p) => PrimeField (int `Mod` p)
-- and newtypes of int `Mod` p.
type PrimeField x =
  ( Modular x
  , Arithmetic x x
  , Finite x
  , Field x
  , Order x ~ Chr x
  )

class AdditiveMonoid a where
  infixl 6 +
  (+) :: a -> a -> a
  zero :: a

sum :: (Foldable t, AdditiveMonoid a) => t a -> a
sum = foldl' (+) zero

class AdditiveMonoid a => AdditiveGroup a where
  negate :: a -> a
  negate a = zero - a
  infixl 6 -
  (-) :: a -> a -> a
  a - b = a + negate b

class MultiplicativeMonoid a where
  infixl 7 *
  (*) :: a -> a -> a
  one :: a

product :: (Foldable t, MultiplicativeMonoid a) => t a -> a
product = foldl' (*) one

class MultiplicativeMonoid a => MultiplicativeGroup a where
  recip :: a -> a
  recip a = one / a
  infixl 7 /
  (/) :: a -> a -> a
  a / b = a * recip b

-- from @Natural is the unique homomorphism from the free Semiring
-- from @Integer is the unique homomorphism from the free Ring
-- from @Rational is the unique homomorphism from the free Field
--
-- prop> from . from = from
-- prop> from @a @a = id
class From x a where
  from :: x -> a
  default from :: x ~ a => x -> a
  from = id

type Semiring a =
  ( AdditiveMonoid a
  , MultiplicativeMonoid a
  , From Natural a
  , From a a
  , Scalar Natural a
  , Scalar a a
  , Exponent Natural a
  )

type Ring a =
  ( AdditiveGroup a
  , MultiplicativeMonoid a
  , From Natural a
  , From Integer a
  , From a a
  , Scalar Natural a
  , Scalar Integer a
  , Scalar a a
  , Exponent Natural a
  )

type Field a =
  ( AdditiveGroup a
  , MultiplicativeGroup a
  , From Natural a
  , From Integer a
  , From Rational a
  , From a a
  , Scalar Natural a
  , Scalar Integer a
  , Scalar Rational a
  , Scalar a a
  , Exponent Natural a
  , Exponent Integer a
  )

type Algebra x a = (Ring x, Ring a, From x a, Scalar x a)

class Semiring a => SemiEuclidean a where
  divMod :: a -> a -> (a,a)
  div :: a -> a -> a
  div a b = let (divisor,_) = divMod a b in divisor
  mod :: a -> a -> a
  mod a b = let (_,modulus) = divMod a b in modulus
  quotRem :: a -> a -> (a,a)
  quot :: a -> a -> a
  quot a b = let (quotient,_) = quotRem a b in quotient
  rem :: a -> a -> a
  rem a b = let (_,remainder) = quotRem a b in remainder

class (SemiEuclidean a, Ring a) => Euclidean a where
  eea :: a -> a -> (a,a,a)
  default eea :: Eq a => a -> a -> (a,a,a)
  eea = xEuclid one zero zero one where
    xEuclid x0 y0 x1 y1 u v
      | v == zero = (u,x0,y0)
      | otherwise =
        let
          (q , r) = u `divMod` v
          x2 = x0 - q * x1
          y2 = y0 - q * y1
        in
          xEuclid x1 y1 x2 y2 v r
  gcd :: a -> a -> a
  gcd a b = let (d,_,_) = eea a b in d

even :: SemiIntegral a => a -> Bool
even a = a `mod` (from @Natural 2) == zero

odd :: SemiIntegral a => a -> Bool
odd a = a `mod` (from @Natural 2) == one

class Ring a => Discrete a where
  dichotomy :: a -> a -> a
  default dichotomy :: Eq a => a -> a -> a
  dichotomy a b = if a == b then one else zero

class Discrete a => Comparable a where
  trichotomy :: a -> a -> a
  default trichotomy :: Ord a => a -> a -> a
  trichotomy a b = case compare a b of
    LT -> negate one
    EQ -> zero
    GT -> one

-- prop> to . from = id
-- prop> to . to = to
-- prop> to @a @a = id
class Into y a where
  to :: a -> y
  default to :: y ~ a => a -> y
  to = id

-- e.g. `Integer`, `Natural`, `Mod int`
type SemiIntegral a =
  ( Prelude.Ord a
  , SemiEuclidean a
  , Into Rational a
  , Into Integer a
  )
-- e.g. `Integer`, `Mod int`
type Integral a =
  ( Prelude.Ord a
  , Euclidean a
  , Into Rational a
  , Into Integer a
  )
-- e.g. `Mod int` & fixed-width unsigned integer types
type Modular a =
  ( Prelude.Ord a
  , Euclidean a
  , Into Rational a
  , Into Integer a
  , Into Natural a
  )

fromSemiIntegral :: (SemiIntegral a, From Integer b) => a -> b
fromSemiIntegral = from . to @Integer

fromInteger :: From Integer b => Integer -> b
fromInteger = from

-- Type level numbers ---------------------------------------------------------

knownNat :: forall n. KnownNat n => Natural
knownNat = natVal' (proxy# @n)

class
  ( KnownNat (Order a)
  ) => Finite a where
    type Order a :: Natural

order :: forall a. Finite a => Natural
order = knownNat @(Order a)

class
  ( KnownNat (Chr a)
  , Semiring a
  ) => FiniteChr a where
    type Chr a :: Natural

characteristic :: forall a. FiniteChr a => Natural
characteristic = knownNat @(Chr a)

-- Use orphan instances for large publicly verified primes
class KnownNat p => Prime p
-- Use this overlappable instance for small enough primes and testing
instance {-# OVERLAPPABLE #-} (KnownNat p, KnownPrime p) => Prime p

type family KnownPrime p where
  KnownPrime p = If (IsPrime p) (() :: Constraint) (TypeError (NotPrimeError p))

type NotPrimeError p =
  'Text "Error: " ':<>: 'ShowType p ':<>: 'Text " is not a prime number."

type family IsPrime p where
  IsPrime 0 = 'False
  IsPrime 1 = 'False
  IsPrime 2 = 'True
  IsPrime 3 = 'True
  IsPrime n = NotDividesFromTo n 2 (AtLeastSqrt n)

type family NotZero n where
  NotZero 0 = 'False
  NotZero n = 'True

type family NotDividesFromTo dividend divisor0 divisor1 where
  NotDividesFromTo dividend divisor divisor = NotZero (dividend `Type.Mod` divisor)
  NotDividesFromTo dividend divisor0 divisor1 =
    NotZero (dividend `Type.Mod` divisor0) && NotDividesFromTo dividend (divisor0 + 1) divisor1

type family AtLeastSqrt n where
  AtLeastSqrt 0 = 0
  AtLeastSqrt n = 2 ^ (Log2 n `Div` 2 + 1)

-- Rational -------------------------------------------------------------------

instance AdditiveMonoid Rational where
  (+) = (Prelude.+)
  zero = 0

instance AdditiveGroup Rational where
  negate = Prelude.negate
  (-) = (Prelude.-)

instance MultiplicativeMonoid Rational where
  (*) = (Prelude.*)
  one = 1

instance MultiplicativeGroup Rational where
  (/) = (Prelude./)

instance Scalar Natural Rational where
  scale n q = to n * q
  combine = combineN
instance Scalar Integer Rational where
  scale i q = to i * q
  combine = combineZ
instance Scalar Rational Rational where
  scale = (*)
  combine terms =
    let
      coefs = [c | (c,_) <- terms]
      commonDenom :: Integer = product (fmap (denominator . to) coefs)
      clearDenom c = (numerator c * commonDenom) `div` commonDenom
      numerators = fmap (\(c,a) -> (clearDenom (to c), a)) terms
    in
      combine numerators / from commonDenom

instance Exponent Natural Rational where
  exponent = (Prelude.^)
  evalMono = evalMonoN
instance Exponent Integer Rational where
  exponent = (Prelude.^^)
  evalMono = evalMonoN . fmap absPow where
    absPow (a,p) =
      let
        pZ = to @Integer p
      in
        if pZ >= 0
        then (a, Prelude.fromIntegral pZ :: Natural)
        else (one / a, Prelude.fromIntegral (negate pZ))

instance From Rational Rational
instance From Natural Rational where from = Prelude.fromIntegral
instance From Integer Rational where from = Prelude.fromInteger
instance Into Rational Rational

instance Discrete Rational
instance Comparable Rational

-- Integer --------------------------------------------------------------------

instance AdditiveMonoid Integer where
  (+) = (Prelude.+)
  zero = 0

instance AdditiveGroup Integer where
  negate = Prelude.negate
  (-) = (Prelude.-)

instance MultiplicativeMonoid Integer where
  (*) = (Prelude.*)
  one = 1

instance Scalar Natural Integer where
  scale n z = to n * z
  combine = combineN
instance Scalar Integer Integer where
  scale = (*)
  combine = combineZ

instance Exponent Natural Integer where
  exponent = (Prelude.^)
  evalMono = evalMonoN

instance From Integer Integer
instance From Natural Integer where from = Prelude.fromIntegral
instance Into Rational Integer where to = Prelude.toRational
instance Into Integer Integer

instance Discrete Integer
instance Comparable Integer

instance SemiEuclidean Integer where
  divMod = Prelude.divMod
  quotRem = Prelude.quotRem
instance Euclidean Integer

-- Natural --------------------------------------------------------------------

instance AdditiveMonoid Natural where
  (+) = (Prelude.+)
  zero = 0

instance MultiplicativeMonoid Natural where
  (*) = (Prelude.*)
  one = 1

instance Scalar Natural Natural where
  scale = (*)
  combine = combineN

instance Exponent Natural Natural where
  exponent = (Prelude.^)
  evalMono = evalMonoN

instance From Natural Natural
instance Into Integer Natural where to = Prelude.toInteger
instance Into Rational Natural where to = Prelude.toRational
instance Into Natural Natural

instance SemiEuclidean Natural where
  divMod = Prelude.divMod
  quotRem = Prelude.quotRem

-- Int ------------------------------------------------------------------------

instance AdditiveMonoid Int where
  (+) = (Prelude.+)
  zero = 0

instance AdditiveGroup Int where
  negate = Prelude.negate
  (-) = (Prelude.-)

instance MultiplicativeMonoid Int where
  (*) = (Prelude.*)
  one = 1

instance Scalar Natural Int where
  scale n z = from n * z
  combine = combineN
instance Scalar Integer Int where
  scale n z = from n * z
  combine = combineZ
instance Scalar Int Int where
  scale = (*)
  combine terms =
    combineZ [(to @Integer c,x) | (c,x) <- terms]

instance Exponent Natural Int where
  exponent = (Prelude.^)
  evalMono = evalMonoN

instance From Int Int
instance From Natural Int where from = Prelude.fromIntegral
instance From Integer Int where from = Prelude.fromIntegral
instance Into Rational Int where to = Prelude.toRational
instance Into Integer Int where to = Prelude.fromIntegral
instance Into Int Int

instance Discrete Int
instance Comparable Int

instance SemiEuclidean Int where
  divMod = Prelude.divMod
  quotRem = Prelude.quotRem
instance Euclidean Int

-- Function -------------------------------------------------------------------

instance {-# OVERLAPPING #-} Semiring a
  => AdditiveMonoid (i -> a) where
    zero = pure zero
    (+) = liftA2 (+)

instance Ring a => AdditiveGroup (i -> a) where
  negate = fmap negate
  (-) = liftA2 (-)

instance MultiplicativeMonoid a => MultiplicativeMonoid (i -> a) where
  one = pure one
  (*) = liftA2 (*)

instance (Scalar c a, Scalar c c, Scalar a a)
  => Scalar (i -> c) (i -> a) where
    scale c a i = scale (c i) (a i)
    combine terms i = combine (fmap (\(c,f) -> (c i, f i)) terms)

instance Semiring a => Scalar Natural (i -> a) where
  scale c f = scale c . f
  combine terms i = combine (fmap (\(c,f) -> (c, f i)) terms)

instance (Semiring a, Scalar Integer a)
  => Scalar Integer (i -> a) where
    scale c f = scale c . f
    combine terms i = combine (fmap (\(c,f) -> (c, f i)) terms)

instance (Semiring a, Scalar Rational a)
  => Scalar Rational (i -> a) where
    scale c f = scale c . f
    combine terms i = combine (fmap (\(c,f) -> (c, f i)) terms)

instance (Exponent pow a) => Exponent pow (i -> a) where
  exponent a p i = exponent (a i) p
  evalMono factors i = evalMono (fmap (\(f,p) -> (f i, p)) factors)

instance MultiplicativeGroup a => MultiplicativeGroup (i -> a) where
  (/) = liftA2 (/)

instance From Natural a => From Natural (i -> a) where
  from = pure . from

instance From Integer a => From Integer (i -> a) where
  from = pure . from

instance From Rational a => From Rational (i -> a) where
  from = pure . from

instance From (i -> a) (i -> a)

instance Discrete a => Discrete (i -> a) where
  dichotomy = liftA2 dichotomy

instance Comparable a => Comparable (i -> a) where
  trichotomy = liftA2 trichotomy

-- Mod ------------------------------------------------------------------------
newtype Mod int n = UnsafeMod {fromMod :: int}
  deriving newtype (Eq, Ord, Prelude.Show)

instance (SemiIntegral int, KnownNat n)
  => AdditiveMonoid (Mod int n) where
    a + b = from (to @Integer a + to b)
    zero = UnsafeMod zero

instance (SemiIntegral int, KnownNat n)
  => AdditiveGroup (Mod int n) where
    negate = from . negate . to @Integer
    a - b = from (to @Integer a - to b)

instance (SemiIntegral int, KnownNat n)
  => MultiplicativeMonoid (Mod int n) where
    a * b = from (to @Integer a * to b)
    one = UnsafeMod one

instance (SemiIntegral int, Prime p)
  => MultiplicativeGroup (Mod int p) where
    recip a = case eea (to @Integer a) (from (knownNat @p)) of
      (_,q,_) -> from q

instance (SemiIntegral int, KnownNat n)
  => SemiEuclidean (Mod int n) where
    divMod a b = case divMod (to @Natural a) (to b) of
      (d,m) -> (from d, from m)
    quotRem a b = case quotRem (to @Natural a) (to b) of
      (q,r) -> (from q, from r)

instance (SemiIntegral int, KnownNat n)
  => Euclidean (Mod int n) where
    eea a b =
      let
        (d,b0,b1) = eea (to @Integer a) (to b)
      in
        (from d, from b0, from b1)

residue :: forall n int. (SemiEuclidean int, KnownNat n) => int -> int
residue int = int `mod` from (knownNat @n)

instance From (Mod int n) (Mod int n)

instance (From Natural int, SemiEuclidean int, KnownNat n)
  => From Natural (Mod int n) where
    from = UnsafeMod . residue @n . from

instance (SemiIntegral int, KnownNat n)
  => From Integer (Mod int n) where
    from = UnsafeMod . from @Natural . Prelude.fromIntegral . residue @n

instance (SemiIntegral int, Prime p)
  => From Rational (Mod int p) where
    from q = from (numerator q) / from (denominator q)

instance Into (Mod int n) (Mod int n)

instance Into int (Mod int n) where
  to = fromMod

instance Into Rational int
  => Into Rational (Mod int n) where
    to = to . fromMod

instance Into Integer int
  => Into Integer (Mod int n) where
    to = to . fromMod

instance SemiIntegral int
  => Into Natural (Mod int n) where
    to = Prelude.fromInteger . to

instance (SemiIntegral int, KnownNat n)
  => Scalar Natural (Mod int n) where
    scale n z = from n * z
    combine = combine . fmap (\(c,a) -> (from @_ @Natural c, a))
instance (SemiIntegral int, KnownNat n)
  => Scalar Integer (Mod int n) where
    scale n z = from n * z
    combine = combine . fmap (\(c,a) -> (from @_ @Integer c, a))
instance (SemiIntegral int, Prime p)
  => Scalar Rational (Mod int p) where
    scale n z = from n * z
    combine = combine . fmap (\(c,a) -> (from @_ @Rational c, a))
instance (SemiIntegral int, KnownNat n)
  => Scalar (Mod int n) (Mod int n) where
    scale = (*)
    combine = combineN . fmap (\(c,a) -> (to @Natural c, a))

instance (SemiIntegral int, KnownNat n)
  => Exponent Natural (Mod int n) where
    exponent a q = exponent a (from @_ @(Mod int n) q)
    evalMono = evalMono . fmap (\(a,q) -> (a,from @_ @(Mod int n) q))

instance (SemiIntegral int, Prime p)
  => Exponent Integer (Mod int p) where
    exponent a q =
      if q >= zero
      then exponent a (from @_ @(Mod int p) q)
      else one / exponent a (from @_ @(Mod int p) (negate q))
    evalMono = evalMono . fmap absPow where
      absPow (a,p) =
        if p >= 0
        then (a, from @_ @(Mod int p) p)
        else (one / a, from (negate p))

instance (SemiIntegral int, KnownNat n)
  => Exponent (Mod int n) (Mod int n) where
    exponent a q = from (to @Natural a ^ to @Natural q)
    evalMono
      = from
      . evalMono
      . fmap (\(a,q) -> (to @Natural a, to @Natural q))

instance (SemiIntegral int, KnownNat n) => Discrete (Mod int n)
instance (SemiIntegral int, KnownNat n) => Comparable (Mod int n)

-- Scalar ------------------------------------------------------------------
class (Semiring c, AdditiveMonoid a)
  => Scalar c a where
    scale :: c -> a -> a
    default scale :: c ~ a => c -> a -> a
    scale = (*)
    combine :: [(c,a)] -> a
    default combine :: c ~ a => [(c,a)] -> a
    combine = sum . fmap (Prelude.uncurry (*))

combineN
  :: (Into Natural c, AdditiveMonoid a)
  => [(c,a)] -> a
combineN combination = combineNat naturalized where
  naturalized = [(to @Natural c, a) | (c,a) <- combination]
  combineNat [] = zero
  combineNat terms =
    let
      halves = combineNat [(c `div` 2, a) | (c,a) <- terms, c > 1]
      halveNots = sum [a | (c,a) <- terms, Prelude.odd c]
    in
      halves + halves + halveNots

combineZ
  :: (Into Integer c, AdditiveGroup a)
  => [(c,a)] -> a
combineZ = combineN . fmap absCoeff where
  absCoeff (c,a) =
    let
      cZ = to @Integer c
    in
      if cZ >= 0
      then (Prelude.fromIntegral cZ :: Natural, a)
      else (Prelude.fromIntegral (negate cZ), negate a)

-- Exponent -------------------------------------------------------------------
class (Semiring pow, MultiplicativeMonoid a)
  => Exponent pow a where
    exponent :: a -> pow -> a
    evalMono :: [(a,pow)] -> a

infixr 8 ^
(^) :: (Exponent Natural a, Into Natural pow) => a -> pow -> a
a ^ b = exponent @Natural a (to b)

infixr 8 ^^
(^^) :: (Exponent Integer a, Into Integer pow) => a -> pow -> a
a ^^ b = exponent @Integer a (to b)

evalMonoN
  :: (Into Natural p, MultiplicativeMonoid a)
  => [(a,p)] -> a
evalMonoN monomial = evalMonoNat naturalized where
  naturalized = [(a, to @Natural p) | (a,p) <- monomial]
  evalMonoNat [] = one
  evalMonoNat factors =
    let
      sqrts = evalMonoNat [(a,p `div` 2) | (a,p) <- factors, p > 1]
      sqrtNots = product [a | (a,p) <- factors, Prelude.odd p]
    in
      sqrts * sqrts * sqrtNots
