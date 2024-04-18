{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Map (
        mapVarArithmeticCircuit,
        mapVarWitness
    ) where

import           Data.Bifunctor                                      (Bifunctor (..))
import           Data.Containers.ListUtils                           (nubOrd)
import           Data.List                                           (sort)
import           Data.Map                                            hiding (drop, foldl, foldr, map, null, splitAt,
                                                                      take)
import           Numeric.Natural                                     (Natural)
import           Prelude                                             hiding (Num (..), drop, length, product, splitAt,
                                                                      sum, take, (!!), (^))

import           ZkFold.Base.Algebra.Polynomials.Multivariate
import           ZkFold.Prelude                                      (elemIndex)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (Arithmetic, ArithmeticCircuit (..), Constraint,
                                                                      ConstraintMonomial)

-- This module contains functions for mapping variables in arithmetic circuits.

mapVar :: [Natural] -> Natural -> Natural
mapVar vars x = case x `elemIndex` vars of
    Just i  -> i
    Nothing -> error "mapVar: something went wrong"

mapVarMonomial :: [Natural] -> ConstraintMonomial -> ConstraintMonomial
mapVarMonomial vars (M as) = M $ mapKeys (mapVar vars) as

mapVarPolynomial :: [Natural] -> Constraint c -> Constraint c
mapVarPolynomial vars (P ms) = P $ map (second $ mapVarMonomial vars) ms

mapVarPolynomials :: [Natural] -> [Constraint c] -> [Constraint c]
mapVarPolynomials vars = map (mapVarPolynomial vars)

mapVarWitness :: [Natural] -> (Map Natural a -> Map Natural a)
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

