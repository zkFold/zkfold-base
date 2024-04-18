{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Base.Data.V where
     
import           Control.Monad.Trans.State        (runState, state)
import           Data.Distributive
import           Data.Functor.Rep
import qualified Data.Vector as V
import           Numeric.Natural                  (Natural)
import           Prelude
import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.ByteString      (Binary (..))
import           Data.Vector.Binary               ()
import           System.Random                    (Random (..))
import           Test.QuickCheck                  (Arbitrary (..))

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

deriving via Representably (Vector dim) instance
  (Field a, KnownNat dim) => VectorSpace a (Vector dim)
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

instance KnownNat dim => Applicative (Vector dim) where
  pure = pureRep
  (<*>) = apRep

instance (KnownNat n, Random a) => Random (Vector n a) where
  random = runState (sequenceA (pureRep (state random)))
  randomR
    = runState
    . sequenceA
    . fmapRep (state . randomR)
    . uncurry mzipRep

instance (Arbitrary a, KnownNat dim) => Arbitrary (Vector dim a) where
    arbitrary = sequenceA (pureRep arbitrary)
