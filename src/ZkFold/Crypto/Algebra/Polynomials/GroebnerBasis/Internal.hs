-- This module is adapted from
-- https://gist.github.com/maksbotan/5414897#file-groebner-hs

module ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis.Internal where

import           Data.List                         (intercalate, foldl', sortBy)
import           Prelude                           hiding (Num(..), (/), (!!), lcm, length, sum, take, drop)

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Prelude                    (length, drop, take, (!!))

data Monom c a = M c [a] deriving (Eq)
newtype Polynom c a = P [Monom c a] deriving (Eq)

instance (Show c, Eq c, FiniteField c, Show a, Eq a, AdditiveGroup a, MultiplicativeMonoid a)
        => Show (Monom c a) where
    show (M c as) = (if c == one then "" else show c) ++
                    intercalate "∙" (map showOne $ filter (\(p,_) -> p /= zero) (zip as [1..]))
        where
            showOne :: (a, Integer) -> String
            showOne (p,i) = "x" ++ show i ++ (if p == one then "" else "^" ++ show p)

instance (Show c, Eq c, FiniteField c, Show a, Eq a, AdditiveGroup a, MultiplicativeMonoid a)
        => Show (Polynom c a) where
    show (P ms) = intercalate " + " $ map show ms

instance (Eq c, Ord a) => Ord (Monom c a) where
    compare (M _ asl) (M _ asr) = compare asl asr

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
    one = P [M one []]

lt :: Polynom c a -> Monom c a
lt (P as) = head as

lv :: (Eq a, AdditiveMonoid a) => Polynom c a -> Integer
lv p = go as
    where
        M _ as = lt p
        go [] = 0
        go (b:bs) = if b == zero then 1 + go bs else 0

zeroM :: (Eq c, FiniteField c) => Monom c a -> Bool
zeroM (M c _) = c == zero

zeroP :: Polynom c a -> Bool
zeroP (P as) = null as

similarM :: (Eq a) => Monom c a -> Monom c a -> Bool
similarM (M _ asl) (M _ asr) = asl == asr

addSimilar :: FiniteField c => Monom c a -> Monom c a -> Monom c a
addSimilar (M cl as) (M cr _) = M (cl+cr) as

mulMono :: (FiniteField c, AdditiveGroup a) => Monom c a -> Monom c a -> Monom c a
mulMono (M cl asl) (M cr asr) = M (cl*cr) (zipWith (+) asl asr)

scale :: FiniteField c => c -> Monom c a -> Monom c a
scale c' (M c as) = M (c*c') as

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

mulPM :: (FiniteField c, AdditiveGroup a) => Polynom c a -> Monom c a -> Polynom c a
mulPM(P as) m = P $ map (mulMono m) as

mulM :: (Eq c, FiniteField c, Ord a, AdditiveGroup a) => Polynom c a -> Polynom c a -> Polynom c a
mulM (P ml) r = foldl' addPoly (P []) $ map (mulPM r) ml

dividable :: (Ord a) => Monom c a -> Monom c a -> Bool
dividable (M _ al) (M _ ar) = and $ zipWith (>=) al ar

divideM :: (FiniteField c, AdditiveGroup a) => Monom c a -> Monom c a -> Monom c a
divideM (M cl al) (M cr ar) = M (cl/cr) (zipWith (-) al ar)

reducable :: (Ord a) => Polynom c a -> Polynom c a -> Bool
reducable l r = dividable (lt l) (lt r)

reduce :: (Eq c, FiniteField c, Ord a, AdditiveGroup a) =>
          Polynom c a -> Polynom c a -> Polynom c a
reduce l r = addPoly l r'
    where r' = mulPM r (scale (negate one) q)
          q = divideM (lt l) (lt r)

reduceMany :: (Eq c, FiniteField c, Ord a, AdditiveGroup a) =>
              Polynom c a -> [Polynom c a] -> Polynom c a
reduceMany h fs = if reduced then reduceMany h' fs else h'
    where (h', reduced) = reduceStep h fs False
          reduceStep p (q:qs) r
              | zeroP h   = (h, r)
              | otherwise =
                    if reducable p q
                        then (reduce p q, True)
                        else reduceStep p qs r
          reduceStep p [] r = (p, r)

lcmM :: (FiniteField c, Ord a) => Monom c a -> Monom c a -> Monom c a
lcmM (M cl al) (M cr ar) = M (cl*cr) (zipWith max al ar)

gcdM :: (FiniteField c, Ord a) => Monom c a -> Monom c a -> Monom c a
gcdM (M cl al) (M cr ar) = M (cl*cr) (zipWith min al ar)

gcdNotOne :: (FiniteField c, Ord a, AdditiveMonoid a) => Monom c a -> Monom c a -> Bool
gcdNotOne l r =
    let M _ as = gcdM l r
    in any (/= zero) as

makeSPoly :: (Eq c, FiniteField c, Ord a, AdditiveGroup a) =>
             Polynom c a -> Polynom c a -> Polynom c a
makeSPoly l r = if gcdNotOne (lt l) (lt r) then addPoly l' r' else zero
    where l'  = mulPM l ra
          r'  = mulPM r la
          lcm = lcmM (lt l) (lt r)
          ra  = divideM lcm (lt l)
          la  = scale (negate one) $ divideM lcm (lt r)

checkOne :: (Eq c, FiniteField c, Ord a, AdditiveGroup a) =>
            Polynom c a -> [Polynom c a] -> [Polynom c a] -> [Polynom c a]
checkOne f checked@(c:cs) add =
    if zeroP s
        then checkOne f cs add
        else s : checkOne f cs (add ++ [s])
    where s = reduceMany (makeSPoly f c) (checked++add)
checkOne _ [] _ = []

makeGroebner :: (Eq c, FiniteField c, Ord a, AdditiveGroup a) =>
                [Polynom c a] -> [Polynom c a]
makeGroebner []     = []
makeGroebner (b:bs) = build [b] bs
    where build checked add@(a:as) = build (checked ++ [a]) (as ++ checkOne a checked add)
          build checked []         = checked

------------------------------------------------------------------------

fullReduceMany :: (Eq c, FiniteField c, Ord a, AdditiveGroup a) =>
    Polynom c a -> [Polynom c a] -> Polynom c a
fullReduceMany h fs
    | zeroP h'   = h'
    | otherwise = P [lt h'] + fullReduceMany (h' - P [lt h']) fs
    where h' = reduceMany h fs

varNumber :: Polynom c a -> Integer
varNumber (P [])         = 0
varNumber (P (M _ as:_)) = length as

varIsMissing :: (Ord a, AdditiveGroup a) => Integer -> Polynom c a -> Bool
varIsMissing i (P ms) = all (\(M _ as) -> as !! (i-1) == zero) ms

checkVarUnique :: (Ord a, AdditiveGroup a) => Integer -> [Polynom c a] -> Bool
checkVarUnique i fs = length (filter (== False) $ map (varIsMissing i) fs) == 1

checkLTSimple :: (Ord a, AdditiveGroup a) => Integer -> Polynom c a -> Bool
checkLTSimple _ (P [])         = True
checkLTSimple i (P (M _ as:_)) = all (== zero) $ take (i-1) as ++ drop i as

trimSystem :: (Eq c, Ord a, AdditiveGroup a) => Polynom c a -> [Polynom c a] -> [Polynom c a]
trimSystem h fs = filter (\f -> lv f >= lv h) $ 
        go (varNumber h)
    where
        go 0 = fs
        go i = if varIsMissing i h && checkVarUnique i fs && any (checkLTSimple i) fs
            then trimSystem h (filter (varIsMissing i) fs)
            else go (i-1)

addSPolyStep :: (Eq c, FiniteField c, Ord a, AdditiveGroup a) =>
            [Polynom c a] -> [Polynom c a] -> [Polynom c a] -> [Polynom c a]
addSPolyStep [] _ rs = rs
addSPolyStep _ [] rs = rs
addSPolyStep (p:ps) (q:qs) rs
    | not (zeroP s)  = sortBy (flip compare) (s : rs')
    | lt p == lt q   = addSPolyStep ps (reverse rs) rs
    | otherwise      = addSPolyStep (p:ps) qs rs
        where
            s = fullReduceMany (makeSPoly p q) rs
            rs' = filter (not . zeroP) $ map (`fullReduceMany` [s]) rs

groebnerStep :: (Eq c, FiniteField c, Ord a, AdditiveGroup a) =>
                Polynom c a -> [Polynom c a] -> (Polynom c a, [Polynom c a])
groebnerStep h fs
    | zeroP h   = (h, fs)
    | otherwise =
        let h'   = fullReduceMany h fs
            fs'  = trimSystem h' fs
            fs'' = addSPolyStep (reverse fs') (reverse fs') fs'
        in (h', fs'')