{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Base.Data.Vector where

import           Control.DeepSeq                  (NFData)
import           Control.Monad.State.Strict       (runState, state)
import           Control.Parallel.Strategies      (parMap, rpar)
import           Data.Aeson                       (ToJSON (..))
import           Data.Distributive                (Distributive (..))
import           Data.Foldable                    (fold)
import           Data.Functor.Rep                 (Representable (..), collectRep, distributeRep, mzipRep, pureRep)
import           Data.These                       (These (..))
import qualified Data.Vector                      as V
import           Data.Vector.Binary               ()
import qualified Data.Vector.Split                as V
import           Data.Zip                         (Semialign (..), Zip (..))
import           GHC.Generics                     (Generic)
import           GHC.IsList                       (IsList (..))
import           Prelude                          hiding (concat, drop, head, length, mod, replicate, sum, tail, take,
                                                   zip, zipWith, (*))
import           System.Random                    (Random (..))
import           Test.QuickCheck                  (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.ByteString      (Binary (..))
import           ZkFold.Prelude                   (length)

newtype Vector (size :: Natural) a = Vector {toV :: V.Vector a}
    deriving (Show, Eq, Functor, Foldable, Traversable, Generic, NFData, Ord)

-- helper
knownNat :: forall size n . (KnownNat size, Integral n) => n
knownNat = fromIntegral (value @size)

instance KnownNat size => Representable (Vector size) where
  type Rep (Vector size) = Zp size
  index (Vector v) ix = v V.! (fromIntegral (fromZp ix))
  tabulate f = Vector (V.generate (knownNat @size) (f . fromIntegral))

instance KnownNat size => Distributive (Vector size) where
  distribute = distributeRep
  collect = collectRep


vtoVector :: forall size a . KnownNat size => V.Vector a -> Maybe (Vector size a)
vtoVector as
  | V.length as == knownNat @size = Just $ Vector as
  | otherwise                     = Nothing

instance IsList (Vector n a) where
    type Item (Vector n a) = a
    toList = fromVector
    fromList = unsafeToVector

toVector :: forall size a . KnownNat size => [a] -> Maybe (Vector size a)
toVector as
    | length as == value @size = Just $ Vector (V.fromList as)
    | otherwise                = Nothing

unsafeToVector :: forall size a . [a] -> Vector size a
unsafeToVector = Vector . V.fromList

unfold :: forall size a b. KnownNat size => (b -> (a, b)) -> b -> Vector size a
unfold f = Vector . V.take (knownNat @size) . V.unfoldr (Just . f)

fromVector :: Vector size a -> [a]
fromVector (Vector as) = V.toList as

(!!) :: Vector size a -> Natural -> a
(Vector as) !! i = as V.! fromIntegral i

uncons :: Vector size a -> (a, Vector (size - 1) a)
uncons (Vector lst) = (V.head lst, Vector $ V.tail lst)

reverse :: Vector size a -> Vector size a
reverse (Vector lst) = Vector (V.reverse lst)

head :: Vector size a -> a
head (Vector as) = V.head as

tail :: Vector size a -> Vector (size - 1) a
tail (Vector as) = Vector $ V.tail as

singleton :: a -> Vector 1 a
singleton = Vector . pure

item :: Vector 1 a -> a
item = head

mapWithIx :: forall n a b . KnownNat n => (Natural -> a -> b) -> Vector n a -> Vector n b
mapWithIx f (Vector l) = Vector $ V.zipWith f (V.enumFromTo 0 (value @n -! 1)) l

mapMWithIx :: forall n m a b . (KnownNat n, Monad m) => (Natural -> a -> m b) -> Vector n a -> m (Vector n b)
mapMWithIx f (Vector l) = Vector <$> V.zipWithM f (V.enumFromTo 0 (value @n -! 1)) l

zipWithM :: forall n m a b c . Applicative m => (a -> b -> m c) -> Vector n a -> Vector n b -> m (Vector n c)
zipWithM f (Vector l) (Vector r) = sequenceA . Vector $ V.zipWith f l r

-- TODO: Check that n <= size?
take :: forall n size a. KnownNat n => Vector size a -> Vector n a
take (Vector lst) = Vector (V.take (knownNat @n) lst)

drop :: forall n m a. KnownNat n => Vector (n + m) a -> Vector m a
drop (Vector lst) = Vector (V.drop (knownNat @n) lst)

splitAt :: forall n m a. KnownNat n => Vector (n + m) a -> (Vector n a, Vector m a)
splitAt (Vector lst) = (Vector (V.take (knownNat @n) lst), Vector (V.drop (knownNat @n) lst))

rotate :: forall size a. KnownNat size => Vector size a -> Integer -> Vector size a
rotate (Vector lst) n = Vector (r <> l)
    where
        len :: Integer
        len = fromIntegral $ value @size

        lshift :: Int
        lshift = fromIntegral $ n `mod` len

        (l, r) = V.splitAt lshift lst

shift :: forall size a. KnownNat size => Vector size a -> Integer -> a -> Vector size a
shift (Vector lst) n pad
  | n < 0 = Vector $ V.take (knownNat @size) (padList <> lst)
  | otherwise = Vector $ V.drop (fromIntegral n) (lst <> padList)
    where
        padList = V.replicate (fromIntegral $ abs n) pad

vectorDotProduct :: forall size a . Semiring a => Vector size a -> Vector size a -> a
vectorDotProduct (Vector as) (Vector bs) = sum $ zipWith (*) as bs

empty :: Vector 0 a
empty = Vector V.empty

infixr 5 .:
(.:) :: a -> Vector n a -> Vector (n + 1) a
a .: (Vector lst) = Vector (a `V.cons` lst)

append :: Vector m a -> Vector n a -> Vector (m + n) a
append (Vector l) (Vector r) = Vector (l <> r)

concat :: Vector m (Vector n a) -> Vector (m * n) a
concat = Vector . V.concatMap toV . toV

unsafeConcat :: forall m n a . [Vector n a] -> Vector (m * n) a
unsafeConcat = concat . unsafeToVector @m

chunks :: forall m n a . KnownNat n => Vector (m * n) a -> Vector m (Vector n a)
chunks (Vector vectors) = unsafeToVector (Vector <$> V.chunksOf (fromIntegral $ value @n) vectors)

instance (KnownNat n, Binary a) => Binary (Vector n a) where
    put = fold . V.map put . toV
    get = Vector <$> V.replicateM (knownNat @n) get

instance KnownNat size => Applicative (Vector size) where
    pure a = Vector $ V.replicate (knownNat @size) a

    (Vector fs) <*> (Vector as) = Vector $ V.zipWith ($) fs as

instance Semialign (Vector size) where
    align (Vector as) (Vector bs) = Vector $ V.zipWith These as bs

instance Zip (Vector size) where
    zip (Vector as) (Vector bs) = Vector $ V.zip as bs

    zipWith f (Vector as) (Vector bs) = Vector $ V.zipWith f as bs

instance (Arbitrary a, KnownNat size) => Arbitrary (Vector size a) where
    arbitrary = sequenceA (pureRep arbitrary)

instance (Random a, KnownNat size) => Random (Vector size a) where
    random = runState (sequenceA (pureRep (state random)))
    randomR = runState . traverse (state . randomR) . uncurry mzipRep

instance ToJSON a => ToJSON (Vector n a) where
    toJSON (Vector xs) = toJSON xs