{-# LANGUAGE TypeApplications #-}

module ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis (
    Monomial,
    Polynomial,
    monomial,
    polynomial,
    groebner,
    fromR1CS,
    verify,
    -- * Internal
    -- TODO: Remove these and add wrappers if necessary.
    lt,
    zeroM,
    zeroP,
    similarM,
    makeSPoly,
    reduce,
    reduceMany,
    reducable,
    fullReduceMany,
    systemReduce,
    mShow,
    pShow,
    var,
    trimSystem,
    varNumber,
    varIsMissing,
    checkVarUnique,
    groebnerStep
    ) where

import           Data.List                         (sortBy, intercalate)
import           Data.Map                          (Map, toList, elems, empty, singleton)
import           Prelude                           hiding (Num(..), length, replicate)

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Algebra.Basic.Field (Zp)
import           ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis.Internal
import           ZkFold.Crypto.Protocol.Arithmetization.R1CS

type Monomial p = Monom (Zp p) Integer

-- TODO: Check the list length.
monomial :: Zp p -> Map Integer Integer -> Monomial p
monomial = M

type Polynomial p = Polynom (Zp p) Integer

polynomial :: Prime p => [Monomial p] -> Polynomial p
polynomial = P . sortBy (flip compare) . filter (not . zeroM)

groebner :: Prime p => [Polynomial p] -> [Polynomial p]
groebner = makeGroebner . sortBy (flip compare)

fromR1CS :: forall p t s . Prime p => R1CS (Zp p) t s -> (Polynomial p, [Polynomial p])
fromR1CS r = (p0, ps)
    where
        m  = r1csSystem r
        xs = reverse $ elems $ r1csVarOrder r
        ps = systemReduce $ 
            sortBy (flip compare) $ map (fromR1CS' @p xs) $ elems m
        j  = head $ r1csOutput r
        p0 = polynomial [var xs j one] - polynomial [var xs 0 one]

verify :: forall p . Prime p => (Polynomial p, [Polynomial p]) -> Bool
verify (p0, ps) = zeroP $ fst $ foldl (\args _ -> uncurry groebnerStep args) (p0, ps) [1::Integer ..200]

-------------------------------------------------------------------------------

mapVars :: [Integer] -> Integer -> Integer
mapVars xs x
    | x == 0    = 0
    | otherwise = case lookup x (zip xs [1..]) of
        Just i  -> i
        Nothing -> error $ "mapVars: variable " ++ show x ++ " not found!"

var :: [Integer] -> Integer -> Zp p -> Monomial p
var xs i v = 
    let j = mapVars xs i
    in M v $ if j > 0 then singleton j 1 else empty

fromR1CS' :: Prime p => [Integer] -> (Map Integer (Zp p), Map Integer (Zp p), Map Integer (Zp p)) -> Polynomial p
fromR1CS' xs (a, b, c) = mulM pa pb `addPoly` mulPM pc (M (negate 1) empty)
    where
        pa = polynomial $ map (uncurry $ var xs) $ toList a
        pb = polynomial $ map (uncurry $ var xs) $ toList b
        pc = polynomial $ map (uncurry $ var xs) $ toList c

mShow :: Monomial p -> String
mShow (M c as) = "m" ++ show c ++ "^" ++ show as

pShow :: Polynomial p -> String
pShow (P ms) = intercalate " + " $ map mShow ms