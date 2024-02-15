{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Map (
        mapVarArithmeticCircuit,
        mapVarWitness
    ) where

import           Data.Bifunctor                                        (Bifunctor(..))
import           Data.Containers.ListUtils                             (nubOrd)
import           Data.List                                             (sort)
import           Data.Map                                              hiding (take, drop, splitAt, foldl, null, map, foldr)
import           Prelude                                               hiding (Num (..), (^), (!!), sum, take, drop, splitAt, product, length)

import           ZkFold.Base.Algebra.Polynomials.Multivariate
import           ZkFold.Prelude                                        (elemIndex)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal   (Arithmetic, ArithmeticCircuit(..), ConstraintMonomial, Constraint)

-- This module contains functions for mapping variables in arithmetic circuits.

mapVar :: [Integer] -> Integer -> Integer
mapVar vars x = case x `elemIndex` vars of
    Just i  -> i
    Nothing -> error "mapVar: something went wrong"

mapVarMonomial :: [Integer] -> ConstraintMonomial -> ConstraintMonomial
mapVarMonomial vars (M as) = M $ mapKeys (mapVar vars) as

mapVarPolynomial :: [Integer] -> Constraint c -> Constraint c
mapVarPolynomial vars (P ms) = P $ map (second $ mapVarMonomial vars) ms

mapVarPolynomials :: [Integer] -> [Constraint c] -> [Constraint c]
mapVarPolynomials vars = map (mapVarPolynomial vars)

mapVarWitness :: [Integer] -> (Map Integer a -> Map Integer a)
mapVarWitness vars = mapKeys (mapVar vars)

mapVarArithmeticCircuit :: Arithmetic a => ArithmeticCircuit a -> ArithmeticCircuit a
mapVarArithmeticCircuit ac =
    let vars = nubOrd $ sort $ 0 : concatMap variables (elems $ acSystem ac)
    in ac
    {
        acSystem  = fromList $ zip [0..] $ mapVarPolynomials vars $ elems $ acSystem ac,
        -- TODO: the new arithmetic circuit expects the old input variables! We should make this safer.
        acWitness = mapVarWitness vars . acWitness ac,
        acOutput  = mapVar vars $ acOutput ac
    }