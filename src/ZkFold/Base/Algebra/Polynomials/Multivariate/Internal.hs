{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DerivingStrategies #-}

module ZkFold.Base.Algebra.Polynomials.Multivariate.Internal where

import           Data.Aeson                        (FromJSON, ToJSON)
import           Data.List                         (intercalate, foldl')
import           Data.Map                          (Map, toList, empty, unionWith, keys, isSubmapOfBy, intersectionWith, differenceWith)
import qualified Data.Map                          as Map
import           GHC.Generics                      (Generic)
import           Prelude                           hiding (Num(..), (/), (!!), lcm, length, sum, take, drop)
import           Test.QuickCheck                   (Arbitrary (..))

import           ZkFold.Base.Algebra.Basic.Class

newtype Var c a = Var a
    deriving newtype (FromJSON, ToJSON)
instance AdditiveSemigroup a => AdditiveSemigroup (Var c a) where
    Var x + Var y = Var (x + y)
instance AdditiveMonoid a => AdditiveMonoid (Var c a) where
    zero = Var zero
instance MultiplicativeSemigroup a => MultiplicativeSemigroup (Var c a) where
    Var x * Var y = Var (x * y)
instance MultiplicativeMonoid a => MultiplicativeMonoid (Var c a) where
    one = Var one
instance (Show a, MultiplicativeMonoid a) => Show (Var c a) where
    show = show . getPower
instance (Eq a, MultiplicativeMonoid a) => Eq (Var c a) where
    (==) vx vy = getPower vx == getPower vy
instance (Ord a, MultiplicativeMonoid a) => Ord (Var c a) where
    compare vx vy = compare (getPower vx) (getPower vy)
instance Arbitrary a => Arbitrary (Var c a) where
    arbitrary = error "arbitrary not implemented for Var"

getPower :: Var c a -> a
getPower (Var j) = j

setPower :: a -> Var c a -> Var c a
setPower j _ = Var j

data Monom c a = M c (Map Integer (Var c a))
    deriving (Eq, Generic, FromJSON, ToJSON)
newtype Polynom c a = P [Monom c a]
    deriving (Eq)
    deriving newtype (FromJSON, ToJSON)

instance (Show c, Eq c, FiniteField c, Show a, Eq a, AdditiveGroup a, MultiplicativeMonoid a)
        => Show (Monom c a) where
    show (M c as) = (if c == one then "" else show c) ++
                    intercalate "∙" (map showOne $ toList as)
        where
            showOne :: (Integer, Var c a) -> String
            showOne (i, p) = "x" ++ show i ++ (if getPower p == one then "" else "^" ++ show p)

instance (Show c, Eq c, FiniteField c, Show a, Eq a, AdditiveGroup a, MultiplicativeMonoid a)
        => Show (Polynom c a) where
    show (P ms) = intercalate " + " $ map show ms

instance (Eq c, Ord a, MultiplicativeMonoid a) => Ord (Monom c a) where
    compare (M _ asl) (M _ asr) = go (toList asl) (toList asr)
        where
            go [] [] = EQ
            go [] _  = LT
            go _  [] = GT
            go ((k1, a1):xs) ((k2, a2):ys)
                | k1 == k2  = if a1 == a2 then go xs ys else compare a1 a2
                | otherwise = compare k2 k1

instance Arbitrary a => Arbitrary (Monom c a) where
    arbitrary = error "arbitrary not implemented for Monom"

instance (Eq c, Ord a, MultiplicativeMonoid a) => Ord (Polynom c a) where
    compare (P l) (P r) = compare l r

instance Arbitrary a => Arbitrary (Polynom c a) where
    arbitrary = error "arbitrary not implemented for Polynom"

instance (Eq c, FiniteField c, Ord a, MultiplicativeMonoid a) => AdditiveSemigroup (Polynom c a) where
    P l + P r = addPoly (P l) (P r)

instance (Eq c, FiniteField c, Ord a, MultiplicativeMonoid a) => AdditiveMonoid (Polynom c a) where
    zero = P []

instance (Eq c, FiniteField c, Ord a, MultiplicativeMonoid a) => AdditiveGroup (Polynom c a) where
    negate    = scale (negate one :: c)
    P l - P r = addPoly (P l) (negate $ P r)

instance (Eq c, FiniteField c, Ord a, AdditiveGroup a, MultiplicativeMonoid a) => MultiplicativeSemigroup (Polynom c a) where
    P l * P r = mulM (P l) (P r)

instance (Eq c, FiniteField c, Ord a, AdditiveGroup a, MultiplicativeMonoid a) => MultiplicativeMonoid (Polynom c a) where
    one = P [M one empty]

instance (Eq c, FiniteField c, Ord a, MultiplicativeMonoid a) => Scale (Polynom c a) c where
    scale c (P as) = P $ map (scaleM c) as

lt :: Polynom c a -> Monom c a
lt (P as) = head as

lv :: Polynom c a -> Integer
lv p
    | null as   = 0
    | otherwise = head $ keys as
    where M _ as = lt p

oneV :: (Eq a, AdditiveMonoid a) => Var c a -> Bool
oneV v = getPower v == zero

zeroM :: (Eq c, FiniteField c) => Monom c a -> Bool
zeroM (M c _) = c == zero

zeroP :: Polynom c a -> Bool
zeroP (P as) = null as

addPower :: (AdditiveSemigroup a) => Var c a -> Var c a -> Var c a
addPower (Var x) (Var y) = Var (x + y)

subPower :: AdditiveGroup a => Var c a -> Var c a -> Var c a
subPower (Var x) (Var y) = Var (x - y)

scaleM :: FiniteField c => c -> Monom c a -> Monom c a
scaleM c' (M c as) = M (c*c') as

similarM :: (Eq a, MultiplicativeMonoid a) => Monom c a -> Monom c a -> Bool
similarM (M _ asl) (M _ asr) = asl == asr

addSimilar :: FiniteField c => Monom c a -> Monom c a -> Monom c a
addSimilar (M cl as) (M cr _) = M (cl + cr) as

addPoly :: (Eq c, FiniteField c, Ord a, MultiplicativeMonoid a) => Polynom c a -> Polynom c a -> Polynom c a
addPoly (P l) (P r) = P $ go l r
    where
          go [] [] = []
          go as [] = as
          go [] bs = bs
          go (a:as) (b:bs)
            | similarM a b =
              if zeroM (addSimilar a b)
                then go as bs
                else addSimilar a b : go as bs
            | a > b     = a : go as (b:bs)
            | otherwise = b : go (a:as) bs

mulMono :: (FiniteField c, AdditiveGroup a) => Monom c a -> Monom c a -> Monom c a
mulMono (M cl asl) (M cr asr) = M (cl*cr) (unionWith addPower asl asr)

mulPM :: (FiniteField c, AdditiveGroup a) => Polynom c a -> Monom c a -> Polynom c a
mulPM(P as) m = P $ map (mulMono m) as

mulM :: (Eq c, FiniteField c, Ord a, AdditiveGroup a, MultiplicativeMonoid a) => Polynom c a -> Polynom c a -> Polynom c a
mulM (P ml) r = foldl' addPoly (P []) $ map (mulPM r) ml

dividable :: (Ord a, MultiplicativeMonoid a) => Monom c a -> Monom c a -> Bool
dividable (M _ al) (M _ ar) = isSubmapOfBy (<=) ar al

divideM :: (FiniteField c, Eq a, AdditiveGroup a) => Monom c a -> Monom c a -> Monom c a
divideM (M cl al) (M cr ar) = M (cl/cr) (Map.filter (not . oneV) $ differenceWith (\x y -> Just $ subPower x y) al ar)

lcmM :: (FiniteField c, Ord a, MultiplicativeMonoid a) => Monom c a -> Monom c a -> Monom c a
lcmM (M cl al) (M cr ar) = M (cl*cr) (unionWith max al ar)

gcdM :: (FiniteField c, Ord a, MultiplicativeMonoid a) => Monom c a -> Monom c a -> Monom c a
gcdM (M cl al) (M cr ar) = M (cl*cr) (intersectionWith min al ar)
