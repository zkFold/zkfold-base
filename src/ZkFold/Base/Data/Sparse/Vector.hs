module ZkFold.Base.Data.Sparse.Vector where

import           Data.Map                        (Map)
import           Data.Zip                        (Semialign (..), Zip (..))
import           Prelude                         hiding ((*), sum, length, zip, zipWith)
import           Test.QuickCheck                 (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field (Zp)

newtype SVector size a = SVector { fromSVector :: Map (Zp size) a }
    deriving (Show, Eq)

instance Foldable (SVector size) where
    foldr f z (SVector as) = foldr f z as

instance Functor (SVector size) where
    fmap f (SVector as) = SVector $ fmap f as

instance Finite size => Semialign (SVector size) where
    align (SVector as) (SVector bs) = SVector $ align as bs

    alignWith f (SVector as) (SVector bs) = SVector $ alignWith f as bs

instance Finite size => Zip (SVector size) where
    zip (SVector as) (SVector bs) = SVector $ zip as bs

    zipWith f (SVector as) (SVector bs) = SVector $ zipWith f as bs

instance (Finite size, Arbitrary a) => Arbitrary (SVector size a) where
    arbitrary = SVector <$> arbitrary