{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators    #-}

module ZkFold.Base.Data.Vector where

import           Control.DeepSeq                  (NFData)
import qualified Control.Monad as M
import           Data.Bifunctor                   (first)
import qualified Data.List                        as List
import           Data.These                       (These (..))
import           Data.Zip                         (Semialign (..), Zip (..))
import           GHC.Generics                     (Generic)
import           Numeric.Natural                  (Natural)
import           Prelude                          hiding (drop, length, mod, replicate, sum, take, zip, zipWith, (*))
import           System.Random                    (Random (..))
import           Test.QuickCheck                  (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.ByteString      (Binary (..))
import qualified ZkFold.Prelude                   as ZP
import           ZkFold.Prelude                   (length, replicate)

newtype Vector (size :: Natural) a = Vector [a]
    deriving (Show, Eq, Functor, Foldable, Traversable, Generic, NFData)

toVector :: forall size a . KnownNat size => [a] -> Maybe (Vector size a)
toVector as
    | length as == value @size = Just $ Vector as
    | otherwise                = Nothing

unsafeToVector :: forall size a . [a] -> Vector size a
unsafeToVector = Vector

fromVector :: Vector size a -> [a]
fromVector (Vector as) = as

(!!) :: Vector size a -> Natural -> a
(Vector as) !! i = as List.!! fromIntegral i

singleton :: a -> Vector 1 a
singleton = Vector . pure

item :: Vector 1 a -> a
item (Vector [a]) = a
item _            = error "Unreachable"

mapWithIx :: forall n a b . KnownNat n => (Natural -> a -> b) -> Vector n a -> Vector n b
mapWithIx f (Vector l) = Vector $ zipWith f [0 .. (value @n -! 1)] l

mapMWithIx :: forall n m a b . (KnownNat n, Monad m) => (Natural -> a -> m b) -> Vector n a -> m (Vector n b)
mapMWithIx f (Vector l) = Vector <$> M.zipWithM f [0 .. (value @n -! 1)] l

zipWithM :: forall n m a b c . Applicative m => (a -> b -> m c) -> Vector n a -> Vector n b -> m (Vector n c)
zipWithM f (Vector l) (Vector r) = Vector <$> M.zipWithM f l r

-- TODO: Check that n <= size?
take :: forall n size a. KnownNat n => Vector size a -> Vector n a
take (Vector lst) = Vector (ZP.take (value @n) lst)

drop :: forall n size a. KnownNat n => Vector size a -> Vector (size - n) a
drop (Vector lst) = Vector (ZP.drop (value @n) lst)

rotate :: forall size a. KnownNat size => Vector size a -> Integer -> Vector size a
rotate (Vector lst) n = Vector (r <> l)
    where
        len :: Integer
        len = fromIntegral $ value @size

        lshift :: Int
        lshift = fromIntegral $ n `mod` len

        (l, r) = splitAt lshift lst

shift :: forall size a. KnownNat size => Vector size a -> Integer -> a -> Vector size a
shift (Vector lst) n pad
  | n < 0 = Vector $ ZP.take (value @size) (padList <> lst)
  | otherwise = Vector $ ZP.drop (fromIntegral n) (lst <> padList)
    where
        padList = replicate (fromIntegral $ abs n) pad


vectorDotProduct :: forall size a . Semiring a => Vector size a -> Vector size a -> a
vectorDotProduct (Vector as) (Vector bs) = sum $ zipWith (*) as bs

empty :: Vector 0 a
empty = Vector []

infixr 5 .:
(.:) :: a -> Vector n a -> Vector (n + 1) a
a .: (Vector lst) = Vector (a : lst)

append :: Vector m a -> Vector n a -> Vector (m + n) a
append (Vector l) (Vector r) = Vector (l <> r)

concat :: Vector m (Vector n a) -> Vector (m * n) a
concat = Vector . concatMap fromVector

unsafeConcat :: forall m n a . [Vector n a] -> Vector (m * n) a
unsafeConcat = Vector . concatMap fromVector

chunks :: forall m n a . KnownNat n => Vector (m * n) a -> Vector m (Vector n a)
chunks (Vector lists) = Vector (Vector <$> chunksOf (fromIntegral $ value @n) lists)

instance Binary a => Binary (Vector n a) where
    put = put . fromVector
    get = Vector <$> get

instance KnownNat size => Applicative (Vector size) where
    pure a = Vector $ replicate (value @size) a

    (Vector fs) <*> (Vector as) = Vector $ zipWith ($) fs as

instance Semialign (Vector size) where
    align (Vector as) (Vector bs) = Vector $ zipWith These as bs

instance Zip (Vector size) where
    zip (Vector as) (Vector bs) = Vector $ zip as bs

    zipWith f (Vector as) (Vector bs) = Vector $ zipWith f as bs

instance (Arbitrary a, KnownNat size) => Arbitrary (Vector size a) where
    arbitrary = Vector <$> mapM (const arbitrary) [1..value @size]

instance (Random a, KnownNat size) => Random (Vector size a) where
    random g =
        let as = foldl (\(as', g') _ ->
                let (a, g'') = random g'
                in (as' ++ [a], g''))
                ([], g) [1..value @size]
        in first Vector as

    randomR (Vector xs, Vector ys) g =
        let as = fst $ foldl (\((as', g'), (xs', ys')) _ ->
                let (a, g'') = randomR (head xs', head ys') g'
                in ((as' ++ [a], g''), (tail xs', tail ys'))) (([], g), (xs, ys)) [1..value @size]
        in first Vector as
