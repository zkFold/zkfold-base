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
  :: (Representable m, VectorSpace a n)
  => Matrix m n a -> Matrix m n a -> Matrix m n a
(.*) = zipWithV (*)

sum1
  :: (Foldable m, Representable n, AdditiveMonoid a)
  => Matrix m n a -> n a
sum1 (Comp1 as) = foldl (mzipWithRep (+)) (pureRep zero) as

sum2
  :: (Representable m, Representable n, Foldable n, AdditiveMonoid a)
  => Matrix m n a -> m a
sum2 (Comp1 as) = sum1 $ transpose $ Comp1 as

matrixDotProduct
  :: (Foldable m, Representable m, VectorSpace a n, Foldable n)
  => Matrix m n a -> Matrix m n a -> a
matrixDotProduct a b = let Comp1 m = a .* b in sum $ fmap sum m

-- | Matrix multiplication
(.*.)
  :: (VectorSpace a n, Distributive k, Functor m, Functor n, Foldable n)
  => Matrix m n a -> Matrix n k a -> Matrix m k a
a .*. b =
    let Comp1 a' = a
        Comp1 b' = transpose b
    in Comp1 $ fmap (\x -> fmap (dotV x) b') a'
