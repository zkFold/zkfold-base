{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Map (
        mapVarArithmeticCircuit,
        mapVarWitness
    ) where

import           Data.Containers.ListUtils                             (nubOrd)
import           Data.List                                             (sort)
import           Data.Map                                              hiding (take, drop, splitAt, foldl, null, map, foldr)
import           Prelude                                               hiding (Num (..), (^), (!!), sum, take, drop, splitAt, product, length)

import           ZkFold.Base.Algebra.Polynomials.Multivariate          (Polynomial, Monomial, getPowers, getMonomials)
import           ZkFold.Base.Algebra.Polynomials.Multivariate.Internal
import           ZkFold.Prelude                                        (elemIndex)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal   (ArithmeticCircuit(..))

-- This module contains functions for mapping variables in arithmetic circuits.

mapVar :: [Integer] -> Integer -> Integer
mapVar vars x = case x `elemIndex` vars of
    Just i  -> i
    Nothing -> error "mapVar: something went wrong"

mapVarMonomial :: [Integer] -> Monomial a -> Monomial a
mapVarMonomial vars (M c as) = M c $ mapKeys (mapVar vars) as

mapVarPolynomial :: [Integer] -> Polynomial a -> Polynomial a
mapVarPolynomial vars (P ms) = P $ map (mapVarMonomial vars) ms

mapVarPolynomials :: [Integer] -> [Polynomial a] -> [Polynomial a]
mapVarPolynomials vars = map (mapVarPolynomial vars)

mapVarWitness :: [Integer] -> (Map Integer a -> Map Integer a)
mapVarWitness vars = mapKeys (mapVar vars)

mapVarArithmeticCircuit :: ArithmeticCircuit a -> ArithmeticCircuit a
mapVarArithmeticCircuit ac =
    let vars = nubOrd $ sort $ 0 : concatMap (keys . getPowers) (concatMap getMonomials $ acSystem ac)
    in ac
    {
        acSystem  = fromList $ zip [0..] $ mapVarPolynomials vars $ elems $ acSystem ac,
        -- TODO: the new arithmetic circuit expects the old input variables! We should make this safer.
        acWitness = mapVarWitness vars . acWitness ac,
        acOutput  = mapVar vars $ acOutput ac
    }