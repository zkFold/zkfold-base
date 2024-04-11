{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module ZkFold.Base.Data.Vector where

import           Data.Bifunctor                   (first)
import           Data.These                       (These (..))
import           Data.Zip                         (Semialign (..), Zip (..))
import           Numeric.Natural                  (Natural)
import           Prelude                          hiding (length, replicate, sum, zip, zipWith, (*))
import           System.Random                    (Random (..))
import           Test.QuickCheck                  (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.ByteString      (ToByteString (..))
import           ZkFold.Prelude                   (length, replicate)

newtype Vector (size :: Natural) a = Vector [a]
  deriving (Show, Eq, Functor, Foldable, Traversable)

toVector :: forall size a. (KnownNat size) => [a] -> Maybe (Vector size a)
toVector as
  | length as == value @size = Just $ Vector as
  | otherwise = Nothing

fromVector :: Vector size a -> [a]
fromVector (Vector as) = as

vectorDotProduct :: forall size a. (Semiring a) => Vector size a -> Vector size a -> a
vectorDotProduct (Vector as) (Vector bs) = sum $ zipWith (*) as bs

concat :: Vector m (Vector n a) -> Vector (m * n) a
concat = Vector . concatMap fromVector

instance (ToByteString a) => ToByteString (Vector n a) where
  toByteString = toByteString . fromVector

instance (KnownNat size) => Applicative (Vector size) where
  pure a = Vector $ replicate (value @size) a

  (Vector fs) <*> (Vector as) = Vector $ zipWith ($) fs as

instance Semialign (Vector size) where
  align (Vector as) (Vector bs) = Vector $ zipWith These as bs

instance Zip (Vector size) where
  zip (Vector as) (Vector bs) = Vector $ zip as bs

  zipWith f (Vector as) (Vector bs) = Vector $ zipWith f as bs

instance (Arbitrary a, KnownNat size) => Arbitrary (Vector size a) where
  arbitrary = Vector <$> mapM (const arbitrary) [1 .. value @size]

instance (Random a, KnownNat size) => Random (Vector size a) where
  random g =
    let as =
          foldl
            ( \(as', g') _ ->
                let (a, g'') = random g'
                 in (as' ++ [a], g'')
            )
            ([], g)
            [1 .. value @size]
     in first Vector as

  randomR (Vector xs, Vector ys) g =
    let as =
          fst $
            foldl
              ( \((as', g'), (xs', ys')) _ ->
                  let (a, g'') = randomR (head xs', head ys') g'
                   in ((as' ++ [a], g''), (tail xs', tail ys'))
              )
              (([], g), (xs, ys))
              [1 .. value @size]
     in first Vector as
