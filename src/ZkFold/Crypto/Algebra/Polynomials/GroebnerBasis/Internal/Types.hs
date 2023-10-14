module ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis.Internal.Types where

import           Data.List                         (intercalate, foldl')
import           Data.Map                          (Map, toList, empty, unionWith, keys)
import           Prelude                           hiding (Num(..), (/), (!!), lcm, length, sum, take, drop)

import           ZkFold.Crypto.Algebra.Basic.Class

data Var c a = Free a | Bound a Integer
instance Show a => Show (Var c a) where
    show = show . getPower
instance Eq a => Eq (Var c a) where
    (==) vx vy = getPower vx == getPower vy
instance Ord a => Ord (Var c a) where
    compare vx vy = compare (getPower vx) (getPower vy)
instance AdditiveSemigroup a => AdditiveSemigroup (Var c a) where
    (Bound x p) + (Bound y _) = Bound (x + y) p
    (Free x) + (Free y)       = Free (x + y)
    _ + _                     = error "AdditiveSemigroup: VarType mismatch"
instance AdditiveMonoid a => AdditiveMonoid (Var c a) where
    zero = Free zero
instance AdditiveGroup a => AdditiveGroup (Var c a) where
    negate (Bound x p) = Bound (negate x) p
    negate (Free x)    = Free (negate x)

getPower :: Var c a -> a
getPower (Bound j _) = j
getPower (Free j)    = j

getPoly :: Var c a -> Integer
getPoly (Bound _ p) = p
getPoly _           = error "getPoly: VarType mismatch"

data Monom c a = M c (Map Integer (Var c a)) deriving (Eq)
newtype Polynom c a = P [Monom c a] deriving (Eq)

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

instance (Eq c, Ord a) => Ord (Monom c a) where
    compare (M _ asl) (M _ asr) = go (toList asl) (toList asr)
        where
            go [] [] = EQ
            go [] _  = LT
            go _  [] = GT
            go ((k1, a1):xs) ((k2, a2):ys)
                | k1 == k2  = if a1 == a2 then go xs ys else compare a1 a2
                | otherwise = compare k2 k1

instance (Eq c, Ord a) => Ord (Polynom c a) where
    compare (P l) (P r) = compare l r

instance (Eq c, FiniteField c, Ord a) => AdditiveSemigroup (Polynom c a) where
    P l + P r = addPoly (P l) (P r)

instance (Eq c, FiniteField c, Ord a) => AdditiveMonoid (Polynom c a) where
    zero = P []

instance (Eq c, FiniteField c, Ord a) => AdditiveGroup (Polynom c a) where
    negate (P as) = P $ map (scale (negate one)) as
    P l - P r     = addPoly (P l) (negate $ P r)

instance (Eq c, FiniteField c, Ord a, AdditiveGroup a) => MultiplicativeSemigroup (Polynom c a) where
    P l * P r = mulM (P l) (P r)

instance (Eq c, FiniteField c, Ord a, AdditiveGroup a) => MultiplicativeMonoid (Polynom c a) where
    one = P [M one empty]

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

scale :: FiniteField c => c -> Monom c a -> Monom c a
scale c' (M c as) = M (c*c') as

similarM :: (Eq a) => Monom c a -> Monom c a -> Bool
similarM (M _ asl) (M _ asr) = asl == asr

addSimilar :: FiniteField c => Monom c a -> Monom c a -> Monom c a
addSimilar (M cl as) (M cr _) = M (cl+cr) as

addPoly :: (Eq c, FiniteField c, Ord a) => Polynom c a -> Polynom c a -> Polynom c a
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
mulMono (M cl asl) (M cr asr) = M (cl*cr) (unionWith (+) asl asr)

mulPM :: (FiniteField c, AdditiveGroup a) => Polynom c a -> Monom c a -> Polynom c a
mulPM(P as) m = P $ map (mulMono m) as

mulM :: (Eq c, FiniteField c, Ord a, AdditiveGroup a) => Polynom c a -> Polynom c a -> Polynom c a
mulM (P ml) r = foldl' addPoly (P []) $ map (mulPM r) ml