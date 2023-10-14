-- This module is adapted from
-- https://gist.github.com/maksbotan/5414897#file-groebner-hs

module ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis.Internal where

import           Data.Bool                         (bool)
import           Data.List                         (sortBy)
import           Data.Map                          (unionWith, isSubmapOfBy, notMember)
import qualified Data.Map                          as Map
import           Prelude                           hiding (Num(..), (/), (!!), lcm, length, sum, take, drop)

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis.Internal.Types
import           ZkFold.Prelude                    (length)

dividable :: (Ord a) => Monom c a -> Monom c a -> Bool
dividable (M _ al) (M _ ar) = isSubmapOfBy (<=) ar al

divideM :: (FiniteField c, Eq a, AdditiveGroup a) => Monom c a -> Monom c a -> Monom c a
divideM (M cl al) (M cr ar) = M (cl/cr) (Map.filter (not . oneV) $ unionWith (-) al ar)

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
lcmM (M cl al) (M cr ar) = M (cl*cr) (unionWith max al ar)

gcdM :: (FiniteField c, Ord a) => Monom c a -> Monom c a -> Monom c a
gcdM (M cl al) (M cr ar) = M (cl*cr) (unionWith min al ar)

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

------------------------------------------------------------------------

fullReduceMany :: (Eq c, FiniteField c, Ord a, AdditiveGroup a) =>
    Polynom c a -> [Polynom c a] -> Polynom c a
fullReduceMany h fs
    | zeroP h'   = h'
    | otherwise = P [lt h'] + fullReduceMany (h' - P [lt h']) fs
    where h' = reduceMany h fs

systemReduce :: (Eq c, FiniteField c, Ord a, AdditiveGroup a) => [Polynom c a] -> [Polynom c a]
systemReduce = foldr f []
    where f p ps = let p' = fullReduceMany p ps in bool ps (p' : ps) (not $ zeroP p')

varNumber :: Polynom c a -> Integer
varNumber (P [])         = 0
varNumber (P (M _ as:_)) = length as

varIsMissing :: Integer -> Polynom c a -> Bool
varIsMissing i (P ms) = all (\(M _ as) -> notMember (i-1) as) ms

checkVarUnique :: Integer -> [Polynom c a] -> Bool
checkVarUnique i fs = length (filter (== False) $ map (varIsMissing i) fs) == 1

checkLTSimple :: Polynom c a -> Bool
checkLTSimple (P [])         = True
checkLTSimple (P (M _ as:_)) = length as <= 1

trimSystem :: (Eq c, Ord a, AdditiveGroup a) => Polynom c a -> [Polynom c a] -> [Polynom c a]
trimSystem h fs = filter (\f -> lv f >= lv h) $
        go (varNumber h)
    where
        go 0 = fs
        go i = if varIsMissing i h && checkVarUnique i fs && any checkLTSimple fs
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