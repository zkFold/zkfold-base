{-# LANGUAGE DeriveAnyClass               #-}
{-# LANGUAGE NoGeneralisedNewtypeDeriving #-}
{-# LANGUAGE TypeApplications             #-}

module ZkFold.Base.Algebra.Polynomials.Multivariate.Monomial
    ( M(..)
    , Monomial
    , Variable
    ) where

import           Control.DeepSeq                  (NFData)
import           Data.Aeson                       (FromJSON, ToJSON)
import           Data.List                        (intercalate)
import           Data.Map.Strict                  (Map, differenceWith, empty, unionWith)
import qualified Data.Map.Strict                  as Map
import           GHC.Generics                     (Generic)
import           GHC.IsList                       (IsList (..))
import           Numeric.Natural                  (Natural)
import           Prelude                          hiding (Num (..), drop, lcm, length, sum, take, (!!), (/))
import           Test.QuickCheck                  (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector

type Variable i = Ord i

type Monomial i j = (Variable i, Ord j, Semiring j)

-- | Monomial type
newtype M i j m = M m
    deriving (Generic, NFData, FromJSON, ToJSON)

instance Ord i => IsList (M i j (Map i j)) where
    type Item (M i j (Map i j)) = (i, j)
    toList (M m) = toList m
    fromList m = M $ fromList m

instance (Show i, Show j, Monomial i j) => Show (M i j (Map i j)) where
    show (M m) = intercalate "∙" . map showVar $ toList m
        where
            showVar :: (i, j) -> String
            showVar (i, j) = "x" ++ show i ++ (if j == one then "" else "^" ++ show j)

instance (Eq i, Eq j) => Eq (M i j (Map i j)) where
    M asl == M asr = asl == asr

instance (Eq i, Ord i, Ord j) => Ord (M i j (Map i j)) where
    compare (M asl) (M asr) = go (toList asl) (toList asr)
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
    M l * M r = M $ Map.filter (/= zero) $ unionWith (+) l r

instance Monomial i j => Exponent (M i j (Map i j)) Natural where
    (^) = natPow

instance Monomial i j => MultiplicativeMonoid (M i j (Map i j)) where
    one = M empty

instance (Monomial i j, Ring j) => Exponent (M i j (Map i j)) Integer where
    (^) = intPow

instance (Monomial i j, Ring j) => MultiplicativeGroup (M i j (Map i j)) where
    invert (M m) = M $ Map.map negate $ m

    M l / M r = M $ differenceWith f l r
        where f a b = if a == b then Nothing else Just (a - b)
