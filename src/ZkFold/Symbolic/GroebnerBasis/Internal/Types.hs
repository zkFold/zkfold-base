module ZkFold.Symbolic.GroebnerBasis.Internal.Types where

import           Data.List                       (foldl', intercalate)
import           Data.Map                        (Map, differenceWith, empty, intersectionWith, isSubmapOfBy, keys,
                                                  toList, unionWith)
import qualified Data.Map                        as Map
import           Numeric.Natural                 (Natural)
import           Prelude                         hiding (Num (..), drop, lcm, length, sum, take, (!!), (/))

import           ZkFold.Base.Algebra.Basic.Class

data VarType = VarTypeFree | VarTypeBound | VarTypeBoolean deriving (Eq)
instance Show VarType where
    show VarTypeFree    = "Free"
    show VarTypeBound   = "Bound"
    show VarTypeBoolean = "Boolean"

data Var a c = Free a | Bound a Natural | Boolean Natural deriving (Functor)
instance (Show a, MultiplicativeMonoid a) => Show (Var a c) where
    show = show . getPower
instance (Eq a, MultiplicativeMonoid a) => Eq (Var a c) where
    (==) vx vy = getPower vx == getPower vy
instance (Ord a, MultiplicativeMonoid a) => Ord (Var a c) where
    compare vx vy = compare (getPower vx) (getPower vy)

getVarType :: Var a c -> VarType
getVarType (Free _)    = VarTypeFree
getVarType (Bound _ _) = VarTypeBound
getVarType (Boolean _) = VarTypeBoolean

getPower :: MultiplicativeMonoid a => Var a c -> a
getPower (Bound j _) = j
getPower (Boolean _) = one
getPower (Free j)    = j

setPower :: a -> Var a c -> Var a c
setPower j (Bound _ i) = Bound j i
setPower _ (Boolean i) = Boolean i
setPower j (Free _)    = Free j

getPoly :: Var a c -> Natural
getPoly (Bound _ p) = p
getPoly (Boolean p) = p
getPoly _           = error "getPoly: VarType mismatch"

data Monom a c = M c (Map Natural (Var a c)) deriving (Eq, Functor)
newtype Polynom a c = P [Monom a c] deriving (Eq, Functor)

instance (Show c, Eq c, FiniteField c, Show a, Eq a, AdditiveGroup a, MultiplicativeMonoid a)
        => Show (Monom a c) where
    show (M c as) = (if c == one then "" else show c) ++
                    intercalate "∙" (map showOne $ toList as)
        where
            showOne :: (Natural, Var a c) -> String
            showOne (i, p) = "x" ++ show i ++ (if getPower p == one then "" else "^" ++ show p)

instance (Show c, Eq c, FiniteField c, Show a, Eq a, AdditiveGroup a, MultiplicativeMonoid a)
        => Show (Polynom a c) where
    show (P ms) = intercalate " + " $ map show ms

instance (AdditiveMonoid c, Eq c, Ord a, MultiplicativeMonoid a) => Ord (Monom a c) where
    compare (M c1 asl) (M c2 asr)
        | c1 == zero && c2 == zero = EQ
        | c1 == zero               = LT
        | c2 == zero               = GT
        | otherwise                = go (toList asl) (toList asr)
        where
            go [] [] = EQ
            go [] _  = LT
            go _  [] = GT
            go ((k1, a1):xs) ((k2, a2):ys)
                | k1 == k2  = if a1 == a2 then go xs ys else compare a1 a2
                | otherwise = compare k2 k1

instance (AdditiveMonoid c, Eq c, Ord a, MultiplicativeMonoid a) => Ord (Polynom a c) where
    compare (P l) (P r) = compare l r

instance (Eq c, FiniteField c, Ord a, MultiplicativeMonoid a) => AdditiveSemigroup (Polynom a c) where
    P l + P r = addPoly (P l) (P r)

instance (Eq c, FiniteField c, Ord a, MultiplicativeMonoid a) => AdditiveMonoid (Polynom a c) where
    zero = P []

instance (Eq c, FiniteField c, Ord a, MultiplicativeMonoid a) => AdditiveGroup (Polynom a c) where
    negate = scale (-1 :: Integer)
    P l - P r = addPoly (P l) (negate $ P r)

instance (Eq c, FiniteField c, Ord a, AdditiveGroup a, MultiplicativeMonoid a) => MultiplicativeSemigroup (Polynom a c) where
    P l * P r = mulM (P l) (P r)

instance MultiplicativeMonoid (Polynom a c) => Exponent (Polynom a c) Natural where
    (^) = natPow

instance (Eq c, FiniteField c, Ord a, AdditiveGroup a, MultiplicativeMonoid a) => MultiplicativeMonoid (Polynom a c) where
    one = P [M one empty]

lt :: Polynom c a -> Monom c a
lt (P as) = head as

lv :: Polynom c a -> Natural
lv p
    | null as   = 0
    | otherwise = head $ keys as
    where M _ as = lt p

oneV :: (Eq a, AdditiveMonoid a, MultiplicativeMonoid a) => Var a c -> Bool
oneV v = getPower v == zero

zeroM :: (Eq c, FiniteField c) => Monom a c -> Bool
zeroM (M c _) = c == zero

zeroP :: Polynom a c -> Bool
zeroP (P as) = null as

addPower :: (AdditiveSemigroup a) => Var a c -> Var a c -> Var a c
addPower (Bound x p) (Bound y q)
    | p == q = Bound (x + y) p
    | otherwise = error "addPowers: VarType mismatch"
addPower (Boolean p) (Boolean q)
    | p == q = Boolean p
    | otherwise = error "addPowers: VarType mismatch"
addPower (Free x) (Free y)       = Free (x + y)
addPower _ _                     = error "addPowers: VarType mismatch"

subPower :: AdditiveGroup a => Var a c -> Var a c -> Maybe (Var a c)
subPower (Bound x p) (Bound y q)
    | p == q = Just $ Bound (x - y) p
    | otherwise = error "subPower: VarType mismatch"
subPower (Boolean p) (Boolean q)
    | p == q = Nothing
    | otherwise = error "subPower: VarType mismatch"
subPower (Free x) (Free y)       = Just $ Free (x - y)
subPower _ _                     = error "subPower: VarType mismatch"

similarM :: (Eq a, MultiplicativeMonoid a) => Monom a c -> Monom a c -> Bool
similarM (M _ asl) (M _ asr) = asl == asr

addSimilar :: FiniteField c => Monom a c -> Monom a c -> Monom a c
addSimilar (M cl as) (M cr _) = M (cl+cr) as

addPoly :: (Eq c, FiniteField c, Ord a, MultiplicativeMonoid a) => Polynom a c -> Polynom a c -> Polynom a c
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

mulMono :: (FiniteField c, AdditiveMonoid a) => Monom a c -> Monom a c -> Monom a c
mulMono (M cl asl) (M cr asr) = M (cl*cr) (unionWith addPower asl asr)

mulPM :: (FiniteField c, AdditiveMonoid a) => Polynom a c -> Monom a c -> Polynom a c
mulPM (P as) m = P $ map (mulMono m) as

mulM :: (Eq c, FiniteField c, Ord a, AdditiveGroup a, MultiplicativeMonoid a) => Polynom a c -> Polynom a c -> Polynom a c
mulM (P ml) r = foldl' addPoly (P []) $ map (mulPM r) ml

dividable :: (Ord a, MultiplicativeMonoid a) => Monom a c -> Monom a c -> Bool
dividable (M _ al) (M _ ar) = isSubmapOfBy (<=) ar al

divideM :: (FiniteField c, Eq a, Ring a) => Monom a c -> Monom a c -> Monom a c
divideM (M cl al) (M cr ar) = M (cl//cr) (Map.filter (not . oneV) $ differenceWith subPower al ar)

lcmM :: (FiniteField c, Ord a, MultiplicativeMonoid a) => Monom a c -> Monom a c -> Monom a c
lcmM (M cl al) (M cr ar) = M (cl*cr) (unionWith max al ar)

gcdM :: (FiniteField c, Ord a, MultiplicativeMonoid a) => Monom a c -> Monom a c -> Monom a c
gcdM (M cl al) (M cr ar) = M (cl*cr) (intersectionWith min al ar)

