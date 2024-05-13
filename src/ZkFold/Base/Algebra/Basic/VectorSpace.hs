{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Algebra.Basic.VectorSpace where

import           Data.Functor.Identity           (Identity (..))
import           Data.Functor.Rep
import           Data.Kind                       (Type)
import           Data.Void                       (Void, absurd)
import           GHC.Generics                    hiding (Rep)
import           Prelude                         hiding (Num (..), div, divMod, length, mod, negate, product, replicate,
                                                  sum, (/), (^))

import           ZkFold.Base.Algebra.Basic.Class

{- | Class of vector spaces with a basis. More accurately, when @a@ is
a `Field` then @v a@ is a vector space over it. If @a@ is a `Ring` then
we have a free module, rather than a vector space. `VectorSpace` may also be thought of
as a "monorepresentable" class, similar to `Representable` but with a fixed
element type.
-}
class VectorSpace a v where
    {- | The `Basis` for a `VectorSpace`. More accurately, `Basis` will be a spanning
    set with "out-of-bounds" basis elements corresponding with 0.
    -}
    type Basis a v :: Type
    tabulateV :: (Basis a v -> a) -> v a
    indexV :: v a -> Basis a v -> a

addV :: (AdditiveSemigroup a, VectorSpace a v) => v a -> v a -> v a
addV = zipWithV (+)

zeroV :: (AdditiveMonoid a, VectorSpace a v) => v a
zeroV = pureV zero

subtractV :: (AdditiveGroup a, VectorSpace a v) => v a -> v a -> v a
subtractV = zipWithV (-)

negateV :: (AdditiveGroup a, VectorSpace a v) => v a -> v a
negateV = mapV negate

scaleV :: (MultiplicativeSemigroup a, VectorSpace a v) => a -> v a -> v a
scaleV c = mapV (c *)

-- | basis vector e_i
basisV :: (Semiring a, VectorSpace a v, Eq (Basis a v)) => Basis a v -> v a
basisV i = tabulateV $ \j -> if i == j then one else zero

-- | dot product
-- prop> v `dotV` basis i = indexV v i
dotV :: (Semiring a, VectorSpace a v, Foldable v) => v a -> v a -> a
v `dotV` w = sum (zipWithV (*) v w)

mapV :: VectorSpace a v => (a -> a) -> v a -> v a
mapV f = tabulateV . fmap f . indexV

pureV :: VectorSpace a v => a -> v a
pureV = tabulateV . const

zipWithV :: VectorSpace a v => (a -> a -> a) -> v a -> v a -> v a
zipWithV f as bs = tabulateV $ \k ->
  f (indexV as k) (indexV bs k)

-- representable vector space
newtype Representably v (a :: Type) = Representably
  { runRepresentably :: v a }
instance Representable v => VectorSpace a (Representably v) where
    type Basis a (Representably v) = Rep v
    tabulateV = Representably . tabulate
    indexV = index . runRepresentably

-- generic vector space
instance (Generic1 v, VectorSpace a (Rep1 v))
  => VectorSpace a (Generically1 v) where
    type Basis a (Generically1 v) = Basis a (Rep1 v)
    indexV (Generically1 v) i = indexV (from1 v) i
    tabulateV f = Generically1 (to1 (tabulateV f))

instance VectorSpace a v => VectorSpace a (M1 i c v) where
    type Basis a (M1 i c v) = Basis a v
    indexV (M1 v) = indexV v
    tabulateV f = M1 (tabulateV f)

-- zero dimensional vector space
deriving via Representably U1 instance VectorSpace a U1

-- one dimensional vector space
deriving via Representably Identity instance VectorSpace a Identity

-- direct sum of vector spaces
instance (VectorSpace a v, VectorSpace a u)
  => VectorSpace a (v :*: u) where
    type Basis a (v :*: u) = Either (Basis a v) (Basis a u)
    tabulateV f = tabulateV (f . Left) :*: tabulateV (f . Right)
    indexV (a :*: _) (Left  i) = indexV a i
    indexV (_ :*: b) (Right j) = indexV b j

-- tensor product of vector spaces
instance (Representable u, VectorSpace a v)
  => VectorSpace a (u :.: v) where
    type Basis a (u :.: v) = (Rep u, Basis a v)
    tabulateV = Comp1 . tabulate . fmap tabulateV . curry
    indexV (Comp1 fg) (i, j) = indexV (index fg i) j

{- | `FunctionSpace` class of functions between `VectorSpace`s.

The type @FunctionSpace a f => f@ should be equal to some

@(VectorSpace a v0, .. ,VectorSpace a vN) => vN a -> .. -> v1 a -> v0 a@

which via uncurrying is equivalent to

@(VectorSpace a v0, .. ,VectorSpace a vN) => (vN :*: .. :*: v1) a -> v0 a@
-}
class VectorSpace a (OutputSpace a f) => FunctionSpace a f where
  -- | Dually to vector spaces, a linear map enables coindexing,
  -- essentially evaluating it, by tabulating its input
  coindexV :: f -> (InputBasis a f -> a) -> OutputSpace a f a
  -- | And also to cotabulate.
  cotabulateV :: ((InputBasis a f -> a) -> OutputSpace a f a) -> f

type family InputBasis a f where
  InputBasis a (x a -> f) = Either (Basis a x) (InputBasis a f)
  InputBasis a (y a) = Void

type family OutputSpace a f where
  OutputSpace a (x a -> f) = OutputSpace a f
  OutputSpace a (y a) = y

instance {-# OVERLAPPABLE #-}
  ( VectorSpace a y
  , OutputSpace a (y a) ~ y
  , InputBasis a (y a) ~ Void
  ) => FunctionSpace a (y a) where
    coindexV f _ = f
    cotabulateV k = k absurd

instance {-# OVERLAPPING #-}
  ( VectorSpace a x
  , OutputSpace a (x a -> f) ~ OutputSpace a f
  , InputBasis a (x a -> f) ~ Either (Basis a x) (InputBasis a f)
  , FunctionSpace a f
  ) => FunctionSpace a (x a -> f) where
    coindexV f i = coindexV (f (tabulateV (i . Left))) (i . Right)
    cotabulateV k x = cotabulateV (k . either (indexV x))
