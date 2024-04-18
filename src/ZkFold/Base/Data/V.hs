{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Data.V where

import           Data.Distributive
import           Data.Functor.Rep
import           Data.Maybe                       (fromMaybe)
import qualified Data.Vector                      as V
import           Data.Vector.Binary               ()
import           GHC.Generics
import           GHC.TypeNats
import           Prelude
import           System.Random                    (Random (..))
import           Test.QuickCheck                  (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.ByteString      (Binary (..))

newtype Vector (dim :: Natural) a = Vector { fromVector :: V.Vector a }
  deriving stock (Eq,Ord,Show,Read,Functor,Foldable,Traversable)

toVector
  :: forall dim a . KnownNat dim
  => V.Vector a -> Maybe (Vector dim a)
toVector as
    | fromIntegral (V.length as) == value @dim = Just $ Vector as
    | otherwise                                 = Nothing

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

type Matrix m n = Vector m :.: Vector n

transpose
  :: (Functor vm, Distributive vn)
  => (vm :.: vn) a -> (vn :.: vm) a
transpose (Comp1 m) = Comp1 (distribute m)
