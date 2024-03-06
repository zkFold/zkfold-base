{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Data.Matrix where

import           Data.Bifunctor                  (first)
import qualified Data.List                       as List
import           Data.Maybe                      (fromJust)
import           Data.These
import           Data.Zip                        (Semialign (..), Zip (..))
import           Prelude                         hiding (Num(..), sum, length, zip, zipWith)
import           System.Random                   (Random (..))
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

transpose :: forall m n a . (Finite m, Finite n) => Matrix m n a -> Matrix n m a
transpose m = fromJust $ toMatrix @n @m $ List.transpose $ fromMatrix m

outer :: forall m n a b c. (a -> b -> c) -> Vector m a -> Vector n b -> Matrix m n c
outer f a b = Matrix $ fmap (\x -> fmap (f x) b) a

-- | Hadamard (entry-wise) matrix product
(.*) :: MultiplicativeSemigroup a => Matrix m n a -> Matrix m n a -> Matrix m n a
(.*) = zipWith (*)

sum1 :: (Semiring a) => Matrix m n a -> Vector n a
sum1 (Matrix as) = Vector (sum <$> fromVector as)

sum2 :: (Finite m, Finite n, Semiring a) => Matrix m n a -> Vector m a
sum2 (Matrix as) = sum1 $ transpose $ Matrix as

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

instance (Finite m, Finite n) => Applicative (Matrix m n) where
    pure a = Matrix $ pure $ pure a

    (Matrix fs) <*> (Matrix as) = Matrix $ zipWith (<*>) fs as

instance Semialign (Matrix m n) where
    align (Matrix as) (Matrix bs) = Matrix $ zipWith (zipWith These) as bs

    alignWith f (Matrix as) (Matrix bs) = Matrix $ zipWith (zipWith (\a b -> f $ These a b)) as bs

instance Zip (Matrix m n) where
    zip (Matrix as) (Matrix bs) = Matrix $ zipWith zip as bs

    zipWith f (Matrix as) (Matrix bs) = Matrix $ zipWith (zipWith f) as bs

instance (Arbitrary a, Finite m, Finite n) => Arbitrary (Matrix m n a) where
    arbitrary = Matrix <$> arbitrary

instance (Random a, Finite m, Finite n) => Random (Matrix m n a) where
    random g =
        let as = foldl (\(as', g') _ ->
                let (a, g'') = random g'
                in (as' ++ [a], g''))
                ([], g) [1..order @m]
        in first (Matrix . Vector) as

    randomR (Matrix xs, Matrix ys) g =
        let as = fst $ foldl (\((as', g'), (xs', ys')) _ ->
                let (a, g'') = randomR (head xs', head ys') g'
                in ((as' ++ [a], g''), (tail xs', tail ys')))
                (([], g), (fromVector xs, fromVector ys)) [1..order @m]
        in first (Matrix . Vector) as