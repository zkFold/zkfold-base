{-# LANGUAGE TypeApplications #-}

module ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis (
    Monomial,
    Polynomial,
    monomial,
    polynomial,
    groebner,
    fromR1CS,
    -- * Internal
    lt, 
    zeroM,
    zeroP,
    similarM,
    makeSPoly
    ) where

import           Data.Bool                         (bool)
import           Data.List                         (nub, sortBy, sort)
import           Data.Map                          (Map, toList, elems, keys)
import           Prelude                           hiding (Num(..), length, replicate)

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Algebra.Basic.Field (Zp)
import           ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis.Internal
import           ZkFold.Crypto.Protocol.Arithmetization.R1CS
import           ZkFold.Prelude                    (replicate)

type Monomial p = Monom (Zp p) Integer

-- TODO: Check the list length.
monomial :: Zp p -> [Integer] -> Monomial p
monomial = M

type Polynomial p = Polynom (Zp p) Integer

polynomial :: Prime p => [Monomial p] -> Polynomial p
polynomial = P . sortBy (flip compare) . filter (not . zeroM)

groebner :: Prime p => [Polynomial p] -> [Polynomial p]
groebner = makeGroebner . sort

fromR1CS :: forall p t . Prime p => R1CS (Zp p) t -> [Polynomial p]
fromR1CS r = map (fromR1CS' @p n f) $ elems m
    where
        n = r1csSizeM r
        m = r1csSystem r
        f = mapVars $ sort $ nub $ concatMap (\(a, b, c) -> keys a ++ keys b ++ keys c) (elems m)

        -- Returns a function that maps the integers from the list to their indices in the list.
        mapVars :: [Integer] -> (Integer -> Integer)
        mapVars xs = \x -> case lookup x (zip xs [1..]) of
            Just i  -> i
            Nothing -> error "mapVars: variable not found"

fromR1CS' :: Prime p => Integer -> (Integer -> Integer) -> (Map Integer (Zp p), Map Integer (Zp p), Map Integer (Zp p)) -> Polynomial p
fromR1CS' n f (a, b, c) = mulM pa pb `addPoly` mulPM pc (M (negate 1) (replicate n 0))
    where
        pa = polynomial $ map (uncurry var) $ toList a
        pb = polynomial $ map (uncurry var) $ toList b
        pc = polynomial $ map (uncurry var) $ toList c

        var :: Integer -> Zp p -> Monomial p
        var i v = M v $ go n (f i)
            where
                go 0 _ = []
                go k j = bool 0 1 (k == j) : go (k - 1) j