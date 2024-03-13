{-# LANGUAGE TypeApplications #-}

module ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial (
        module ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial.Class,
        M(..)
) where

import           Data.Aeson                        (FromJSON, ToJSON)
import           Data.List                         (intercalate)
import           Data.Map                          (Map, toList, unionWith, differenceWith, empty)
import qualified Data.Map                          as Map
import           GHC.Generics                      (Generic)
import           Prelude                           hiding (Num(..), (/), (!!), lcm, length, sum, take, drop)
import           Test.QuickCheck                   (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial.Class

-- | Monomial type
newtype M i j m = M m
    deriving (Generic, FromJSON, ToJSON)

instance (Show i, Show j, FromMonomial i j m) => Show (M i j m) where
    show (M m) = intercalate "∙" (map showVar (toList $ fromMonomial @i @j @m m))
        where
            showVar :: (i, j) -> String
            showVar (i, j) = "x" ++ show i ++ (if j == one then "" else "^" ++ show j)

instance (FromMonomial i j m) => (Eq (M i j m)) where
    (M asl) == (M asr) = fromMonomial @i @j @m asl == fromMonomial @i @j @m asr

instance (FromMonomial i j m) => Ord (M i j m) where
    compare (M asl) (M asr) = go (toList $ fromMonomial @i @j @m asl) (toList $ fromMonomial @i @j @m asr)
        where
            go [] [] = EQ
            go [] _  = LT
            go _  [] = GT
            go ((k1, a1):xs) ((k2, a2):ys)
                | k1 == k2  = if a1 == a2 then go xs ys else compare a1 a2
                | otherwise = compare k2 k1

instance Arbitrary m => Arbitrary (M i j m) where
    arbitrary = M <$> arbitrary

instance Monomial i j => MultiplicativeSemigroup (M i j (Map i j)) where
    (M l) * (M r) = M $ Map.filter (/= zero) $ unionWith (+) (fromMonomial @i @j l) (fromMonomial @i @j r)

instance Monomial i j => MultiplicativeMonoid (M i j (Map i j)) where
    one = M empty

instance Monomial i j => MultiplicativeGroup (M i j (Map i j)) where
    invert (M m) = M $ Map.map negate $ fromMonomial @i @j m

    (M l) / (M r) = M $ differenceWith f (fromMonomial @i @j l) (fromMonomial @i @j r)
        where f a b = if a == b then Nothing else Just (a - b)
