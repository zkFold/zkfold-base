{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Data.Matrix where

import           Data.Distributive               (Distributive (..))
import           Data.Functor.Rep
import           GHC.Generics                    ((:.:) (..))
import           Prelude                         hiding (sum, (*), (+))

import           ZkFold.Base.Algebra.Basic.Class

-- TODO: implement a proper matrix algebra
-- Could be useful for speeding up the proof computations

type Matrix m n = m :.: n

transpose :: (Functor m, Distributive n) => Matrix m n a -> Matrix n m a
transpose (Comp1 m) = Comp1 (distribute m)

outer
  :: (Functor m, Functor n)
  => (a -> b -> c) -> m a -> n b
  -> Matrix m n c
outer f a b = Comp1 (fmap (\x -> fmap (f x) b) a)

-- | Hadamard (entry-wise) matrix product
(.*)
  :: (Representable m, Representable n, MultiplicativeSemigroup a)
  => Matrix m n a -> Matrix m n a -> Matrix m n a
(.*) = mzipWithRep (*)

sum1
  :: (Foldable m, Representable n, AdditiveMonoid a)
  => Matrix m n a -> n a
sum1 (Comp1 as) = foldl (mzipWithRep (+)) (pureRep zero) as

sum2
  :: (Representable m, Distributive n, Foldable n, AdditiveMonoid a)
  => Matrix m n a -> m a
sum2 (Comp1 as) = sum1 $ transpose $ Comp1 as

matrixDotProduct
  :: (Foldable m, Representable m, Foldable n, Representable n, Semiring a)
  => Matrix m n a -> Matrix m n a -> a
matrixDotProduct a b = let Comp1 m = a .* b in sum $ fmap sum m

-- | Matrix multiplication
(.*.)
  :: (Functor m, Foldable n, Representable n, Distributive k, Semiring a)
  => Matrix m n a -> Matrix n k a -> Matrix m k a
a .*. b =
    let Comp1 a' = a
        Comp1 b' = transpose b
        x `dot` y = sum (mzipWithRep (*) x y)
    in Comp1 $ fmap (\x -> fmap (x `dot`) b') a'
