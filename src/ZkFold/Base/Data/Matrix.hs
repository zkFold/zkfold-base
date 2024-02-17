{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Data.Matrix where

import qualified Data.List                       as List
import           Data.Maybe                      (fromJust)
import           Prelude                         hiding (Num(..), sum, length)
import           Test.QuickCheck                 (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector

-- TODO: implement a proper matrix algebra
-- Could be useful for speeding up the proof computations

newtype Matrix m n a = Matrix (Vector m (Vector n a))
    deriving (Show, Eq)

toMatrix :: forall m n a . (Finite m, Finite n) => [[a]] -> Maybe (Matrix m n a)
toMatrix as = do
    as' <- mapM (toVector @n) as
    Matrix <$> toVector @m as'

fromMatrix :: forall m n a . Matrix m n a -> [[a]]
fromMatrix (Matrix as) = map fromVector $ fromVector as

matrixZipWith :: forall m n a . (a -> a -> a) -> Matrix m n a -> Matrix m n a -> Matrix m n a
matrixZipWith f (Matrix a) (Matrix b) = Matrix $ vectorZipWith (vectorZipWith f) a b

transpose :: forall m n a . (Finite m, Finite n) => Matrix m n a -> Matrix n m a
transpose m = fromJust $ toMatrix @n @m $ List.transpose $ fromMatrix m

outer :: forall m n a b c. (a -> b -> c) -> Vector m a -> Vector n b -> Matrix m n c
outer f a b = Matrix $ fmap (\x -> fmap (f x) b) a

-- | Hadamard (entry-wise) matrix product
(.*) :: MultiplicativeSemigroup a => Matrix m n a -> Matrix m n a -> Matrix m n a
(.*) = matrixZipWith (*)

matrixDotProduct :: forall m n a . Semiring a => Matrix m n a -> Matrix m n a -> a
matrixDotProduct a b = let Matrix m = a .* b in sum $ fmap sum m

-- -- | Matrix multiplication
(.*.) :: (Finite n, Finite k, Semiring a) => Matrix m n a -> Matrix n k a -> Matrix m k a
a .*. b =
    let Matrix a' = a
        Matrix b' = transpose b
    in Matrix $ fmap (\x -> fmap (vectorDotProduct x) b') a'

instance Functor (Matrix m n) where
    fmap f (Matrix as) = Matrix $ fmap (fmap f) as

instance (Arbitrary a, Finite m, Finite n) => Arbitrary (Matrix m n a) where
    arbitrary = Matrix <$> arbitrary