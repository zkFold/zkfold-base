{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Data.Vector where

import           Prelude                         hiding ((*), sum, length)
import           Test.QuickCheck                 (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Prelude                  (length)

newtype Vector size a = Vector [a]
    deriving (Show, Eq)

toVector :: forall size a . Finite size => [a] -> Maybe (Vector size a)
toVector as
    | length as == order @size = Just $ Vector as
    | otherwise                = Nothing

fromVector :: Vector size a -> [a]
fromVector (Vector as) = as

vectorZipWith :: forall size a . (a -> a -> a) -> Vector size a -> Vector size a -> Vector size a
vectorZipWith f (Vector as) (Vector bs) = Vector $ zipWith f as bs

vectorDotProduct :: forall size a . Semiring a => Vector size a -> Vector size a -> a
vectorDotProduct (Vector as) (Vector bs) = sum $ vectorZipWith (*) (Vector as) (Vector bs)

instance Foldable (Vector size) where
    foldr f z (Vector as) = foldr f z as

instance Functor (Vector size) where
    fmap f (Vector as) = Vector $ map f as

instance (Arbitrary a, Finite size) => Arbitrary (Vector size a) where
    arbitrary = Vector <$> mapM (const arbitrary) [1..order @size]