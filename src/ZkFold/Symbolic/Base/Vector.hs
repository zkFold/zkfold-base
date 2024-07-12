{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE QuantifiedConstraints, UndecidableInstances, UndecidableSuperClasses #-}

module ZkFold.Symbolic.Base.Vector
  ( -- * VectorSpace
    VectorSpace (..)
    -- * Vector types
  , Vector (..)
  , SparseV (..), sparseV
  , Gen.U1 (..)
  , Gen.Par1 (..)
  , (Gen.:*:) (..)
  , (Gen.:.:) (..)
    -- * Structure combinators
  , constV
  , zipWithV
    -- * VectorSpace combinators
  , zeroV
  , addV
  , subtractV
  , negateV
  , scaleV
  , dotV
  ) where

import Control.Category
import Control.Monad
import Data.Bool
import Data.Distributive
import Data.Either
import Data.Eq
import Data.Ord
import Data.Foldable hiding (sum)
import Data.Function (const, ($))
import Data.Functor
import Data.Functor.Rep
import Data.Traversable
import Data.Kind (Type)
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Maybe
import Data.Type.Equality
import qualified Data.Vector as V
import Data.Void
import qualified GHC.Generics as Gen
import qualified Prelude

import ZkFold.Symbolic.Base.Num

{- |
Class of vector spaces with a basis.

`VectorSpace` is a known sized "monorepresentable" class,
similar to `Representable` plus `Traversable`,
but with a fixed element type that is a `Field`.

A "vector" in a `VectorSpace` can be thought of as a
tuple of numbers @(x1,..,xn)@.
-}
class
  ( Field a
  , Traversable v
  , Ord (Basis a v)
  ) => VectorSpace a v where
    {- | The `Basis` for a `VectorSpace`. More accurately,
    `Basis` will be a spanning set with "out-of-bounds"
    basis elements corresponding with zero.
    -}

    type Basis a v :: Type
    type Basis a v = Basis a (Gen.Rep1 v)

    tabulateV :: (Basis a v -> a) -> v a
    default tabulateV
      :: ( Gen.Generic1 v
         , VectorSpace a (Gen.Rep1 v)
         , Basis a v ~ Basis a (Gen.Rep1 v)
         )
      => (Basis a v -> a) -> v a
    tabulateV = Gen.to1 . tabulateV

    indexV :: v a -> Basis a v -> a
    default indexV
      :: ( Gen.Generic1 v
         , VectorSpace a (Gen.Rep1 v)
         , Basis a v ~ Basis a (Gen.Rep1 v)
         )
      => v a -> Basis a v -> a
    indexV = indexV . Gen.from1

    dimV :: Natural
    default dimV :: VectorSpace a (Gen.Rep1 v) => Natural
    dimV = dimV @a @(Gen.Rep1 v)

    basisV :: v (Basis a v)
    default basisV
      :: ( Gen.Generic1 v
         , VectorSpace a (Gen.Rep1 v)
         , Basis a v ~ Basis a (Gen.Rep1 v)
         )
      => v (Basis a v)
    basisV = Gen.to1 (basisV @a @(Gen.Rep1 v))

constV :: VectorSpace a v => a -> v a
constV = tabulateV . const

zipWithV :: VectorSpace a v => (a -> a -> a) -> v a -> v a -> v a
zipWithV f as bs = tabulateV $ \k ->
  f (indexV as k) (indexV bs k)

zeroV :: VectorSpace a v => v a
zeroV = constV zero

addV :: VectorSpace a v => v a -> v a -> v a
addV = zipWithV (+)

subtractV :: VectorSpace a v => v a -> v a -> v a
subtractV = zipWithV (-)

negateV :: VectorSpace a v => v a -> v a
negateV = fmap negate

scaleV :: VectorSpace a v => a -> v a -> v a
scaleV c = fmap (c *)

-- | dot product
dotV :: VectorSpace a v => v a -> v a -> a
v `dotV` w = sum (zipWithV (*) v w)

-- generic vector space
instance VectorSpace a v
  => VectorSpace a (Gen.M1 i c v) where
    type Basis a (Gen.M1 i c v) = Basis a v
    indexV (Gen.M1 v) = indexV v
    tabulateV f = Gen.M1 (tabulateV f)
    dimV = dimV @a @v
    basisV = Gen.M1 (basisV @a @v)

-- zero dimensional vector space
instance Field a => VectorSpace a Gen.U1 where
  type Basis a Gen.U1 = Void
  tabulateV = tabulate
  indexV = index
  dimV = zero
  basisV = Gen.U1

-- one dimensional vector space
instance Field a => VectorSpace a Gen.Par1 where
  type Basis a Gen.Par1 = ()
  tabulateV = tabulate
  indexV = index
  dimV = one
  basisV = Gen.Par1 ()

-- direct sum of vector spaces
instance (VectorSpace a v, VectorSpace a u)
  => VectorSpace a (v Gen.:*: u) where
    type Basis a (v Gen.:*: u) = Either (Basis a v) (Basis a u)
    tabulateV f = tabulateV (f . Left) Gen.:*: tabulateV (f . Right)
    indexV (a Gen.:*: _) (Left  i) = indexV a i
    indexV (_ Gen.:*: b) (Right j) = indexV b j
    dimV = dimV @a @v + dimV @a @u
    basisV = fmap Left (basisV @a @v) Gen.:*: fmap Right (basisV @a @u)

-- tensor product of vector spaces
instance
  ( VectorSpace a v
  , VectorSpace a u
  , Representable v
  , Basis a v ~ Rep v
  ) => VectorSpace a (v Gen.:.: u) where
    type Basis a (v Gen.:.: u) = (Basis a v, Basis a u)
    tabulateV = Gen.Comp1 . tabulate . fmap tabulateV . Prelude.curry
    indexV (Gen.Comp1 fg) (i, j) = indexV (index fg i) j
    dimV = dimV @a @v * dimV @a @u
    basisV = Gen.Comp1
      (basisV @a @v <&> \bv -> basisV @a @u <&> \bu -> (bv,bu))

-- | concrete vectors
newtype Vector (n :: Natural) a = UnsafeV (V.Vector a)
  deriving stock
    (Functor, Foldable, Traversable, Eq, Ord)

instance (KnownNat n, Prelude.Show a)
  => Prelude.Show (Vector n a) where
    showsPrec d v
      = Prelude.showParen (d > 10)
      $ Prelude.showString "fromV "
      . Prelude.showsPrec 11 (toList v)

instance KnownNat n => Representable (Vector n) where
  type Rep (Vector n) = Prelude.Int
  index (UnsafeV v) i = v V.! i
  tabulate = UnsafeV . V.generate (from (knownNat @n))

instance KnownNat n => Distributive (Vector n) where
  distribute = distributeRep
  collect = collectRep

instance (Field a, KnownNat n) => VectorSpace a (Vector n) where
  type Basis a (Vector n) = Prelude.Int
  indexV (UnsafeV v) i = fromMaybe zero (v V.!? i)
  tabulateV = tabulate
  dimV = knownNat @n
  basisV = tabulate id

-- | sparse vectors
newtype SparseV (n :: Natural) a =
  UnsafeSparseV {fromSparseV :: IntMap a}
    deriving stock
      (Functor, Traversable, Eq, Ord)

instance Foldable (SparseV n) where
  foldMap f v = foldMap f (fromSparseV v)
  toList _ = Prelude.error "toList @(SparseV _) is an error, use `toListV`."

instance Prelude.Show a => Prelude.Show (SparseV n a) where
  showsPrec d v
    = Prelude.showParen (d > 10)
    $ Prelude.showString "sparseV "
    . Prelude.showsPrec 11 (fromSparseV v)

sparseV :: forall a n. (Eq a, Field a, KnownNat n) => IntMap a -> SparseV n a
sparseV intMap = UnsafeSparseV (IntMap.foldMapWithKey sparsify intMap) where
  sparsify int a =
    if a == zero || int < 0 || int >= from (knownNat @n)
    then IntMap.empty
    else IntMap.singleton int a

instance (Eq a, Field a, KnownNat n) => VectorSpace a (SparseV n) where
  type Basis a (SparseV n) = Prelude.Int
  indexV v i = fromMaybe zero (fromSparseV v IntMap.!? i)
  tabulateV f = UnsafeSparseV $
    IntMap.fromList
      [ (i, f i)
      | i <- [0 .. from (knownNat @n) - 1]
      , f i /= zero
      ]
  dimV = knownNat @n
  basisV = UnsafeSparseV $
    IntMap.fromList
      [ (i, i)
      | i <- [0 .. from (knownNat @n) - 1]
      ]
