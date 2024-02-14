{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Data.Vector where

import           Prelude                         hiding (length)
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

instance (Arbitrary a, Finite size) => Arbitrary (Vector size a) where
    arbitrary = Vector <$> mapM (const arbitrary) [1..order @size]