module ZkFold.Symbolic.GroebnerBasis.Internal where

import           Data.List                                        (sortBy)
import           Data.Map                                         (notMember)
import           Numeric.Natural                                  (Natural)
import           Prelude                                          hiding (Num (..), drop, lcm, length, sum, take, (!!), (/))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Prelude                                   (length)
import           ZkFold.Symbolic.GroebnerBasis.Internal.Reduction
import           ZkFold.Symbolic.GroebnerBasis.Internal.Types

makeSPoly :: (Eq c, FiniteField c, Ord a, Ring a) =>
             Polynom c a -> Polynom c a -> Polynom c a
makeSPoly l r = if null as then zero else addPoly l' r'
    where M _ as = gcdM (lt l) (lt r)
          l'  = mulPM l ra
          r'  = mulPM r la
          lcm = lcmM (lt l) (lt r)
          ra  = divideM lcm (lt l)
          la  = scale (-1 :: Integer) $ divideM lcm (lt r)

varNumber :: Polynom c a -> Natural
varNumber (P [])         = 0
varNumber (P (M _ as:_)) = length as

varIsMissing :: Natural -> Polynom c a -> Bool
varIsMissing i (P ms) = all (\(M _ as) -> notMember (i -! 1) as) ms

checkVarUnique :: Natural -> [Polynom c a] -> Bool
checkVarUnique i fs = length (filter not $ map (varIsMissing i) fs) == 1

checkLTSimple :: Polynom c a -> Bool
checkLTSimple (P [])         = True
checkLTSimple (P (M _ as:_)) = length as <= 1

trimSystem :: (Eq c, Ord a, AdditiveMonoid a) => Polynom c a -> [Polynom c a] -> [Polynom c a]
trimSystem h fs = filter (\f -> lv f >= lv h) $
        go (varNumber h)
    where
        go 0 = fs
        go i = if varIsMissing i h && checkVarUnique i fs && any checkLTSimple fs
            then trimSystem h (filter (varIsMissing i) fs)
            else go (i -! 1)

addSPolyStep :: (Eq c, FiniteField c, Ord a, Ring a) =>
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

groebnerStep :: (Eq c, FiniteField c, Ord a, Ring a) =>
                Polynom c a -> [Polynom c a] -> (Polynom c a, [Polynom c a])
groebnerStep h fs
    | zeroP h   = (h, fs)
    | otherwise =
        let h'   = fullReduceMany h fs
            fs'  = trimSystem h' fs
            fs'' = addSPolyStep (reverse fs') (reverse fs') fs'
        in (h', fs'')

