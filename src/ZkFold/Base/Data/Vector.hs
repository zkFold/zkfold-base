{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Data.Vector where

import           Data.Zip                        (Semialign (..), Zip (..))
import           Data.These
import           Prelude                         hiding ((*), sum, length, zip, zipWith)
import           Test.QuickCheck                 (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.ByteString     (ToByteString(..))
import           ZkFold.Prelude                  (length)

newtype Vector size a = Vector [a]
    deriving (Show, Eq)

toVector :: forall size a . Finite size => [a] -> Maybe (Vector size a)
toVector as
    | length as == order @size = Just $ Vector as
    | otherwise                = Nothing

fromVector :: Vector size a -> [a]
fromVector (Vector as) = as

vectorDotProduct :: forall size a . Semiring a => Vector size a -> Vector size a -> a
vectorDotProduct (Vector as) (Vector bs) = sum $ zipWith (*) as bs

instance ToByteString a => ToByteString (Vector n a) where
    toByteString = toByteString . fromVector

instance Foldable (Vector size) where
    foldr f z (Vector as) = foldr f z as

instance Functor (Vector size) where
    fmap f (Vector as) = Vector $ map f as

instance Semialign (Vector size) where
    align (Vector as) (Vector bs) = Vector $ zipWith These as bs

instance Zip (Vector size) where
    zip (Vector as) (Vector bs) = Vector $ zip as bs

    zipWith f (Vector as) (Vector bs) = Vector $ zipWith f as bs

instance (Arbitrary a, Finite size) => Arbitrary (Vector size a) where
    arbitrary = Vector <$> mapM (const arbitrary) [1..order @size]