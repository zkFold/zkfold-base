{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators    #-}

module ZkFold.Base.Data.Vector where

import           Data.Distributive                (Distributive (..))
import           Data.Functor.Rep
import           Data.Maybe                       (fromMaybe)
import qualified Data.Vector                      as V
import           Data.Vector.Binary               ()
import           Numeric.Natural                  (Natural)
import           Prelude                          hiding (length, replicate, sum, zip, zipWith, (*))
import           System.Random                    (Random (..))
import           Test.QuickCheck                  (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.ByteString      (Binary (..))
import           ZkFold.Prelude                   (length)

newtype Vector (size :: Natural) a = Vector {toV :: V.Vector a}
    deriving (Show, Eq, Functor, Foldable, Traversable)

toVector :: forall size a . KnownNat size => [a] -> Maybe (Vector size a)
toVector = fromV . V.fromList

fromV :: forall size a . KnownNat size => V.Vector a -> Maybe (Vector size a)
fromV as
    | length as == value @size = Just $ Vector as
    | otherwise                = Nothing

fromVector :: Vector size a -> [a]
fromVector = V.toList . toV

concat :: Vector m (Vector n a) -> Vector (m * n) a
concat = Vector . V.concatMap toV . toV

instance Binary a => Binary (Vector n a) where
    put = put . fromVector
    get = Vector <$> get

instance KnownNat dim => Distributive (Vector dim) where
  distribute = distributeRep
  collect = collectRep

instance KnownNat dim => Representable (Vector dim) where
  type Rep (Vector dim) = Int
  tabulate = Vector . V.generate (fromIntegral (value @dim))
  index (Vector xs) i = xs V.! i

instance (Field a, KnownNat dim)
  => VectorSpace a (Vector dim) where
    type Basis a (Vector dim) = Int
    tabulateV = tabulate
    -- safe index; out of bounds -> 0
    indexV (Vector xs) i = fromMaybe zero (xs V.!? i)
deriving via Representably (Vector dim) a instance
  (Field a, KnownNat dim) => AdditiveSemigroup (Vector dim a)
deriving via Representably (Vector dim) a instance
  (Field a, KnownNat dim) => AdditiveMonoid (Vector dim a)
deriving via Representably (Vector dim) a instance
  (Field a, KnownNat dim) => AdditiveGroup (Vector dim a)
deriving via Representably (Vector dim) a instance
  (Field a, KnownNat dim) => Scale Natural (Vector dim a)
deriving via Representably (Vector dim) a instance
  (Field a, KnownNat dim) => Scale Integer (Vector dim a)
deriving via Representably (Vector dim) a instance
  (Field a, KnownNat dim) => Scale a (Vector dim a)
deriving via Representably (Vector dim) instance
  KnownNat dim => Applicative (Vector dim)
deriving via Representably (Vector dim) a instance
  (KnownNat dim, Random a) => Random (Vector dim a)
deriving via Representably (Vector dim) a instance
  (Arbitrary a, KnownNat dim) => Arbitrary (Vector dim a)
