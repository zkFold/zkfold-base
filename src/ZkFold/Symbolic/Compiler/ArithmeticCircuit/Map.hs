{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Map (
        mapVarArithmeticCircuitTest,
        mapVarWitness
    ) where

import           Data.Map                                            hiding (drop, foldl, foldr, fromList, map, null,
                                                                      splitAt, take, toList)
import qualified Data.Map                                            as Map
import           GHC.IsList                                          (IsList (..))
import           Numeric.Natural                                     (Natural)
import           Prelude                                             hiding (Num (..), drop, length, product, splitAt,
                                                                      sum, take, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Class                     (MultiplicativeMonoid (..))
import           ZkFold.Base.Algebra.Polynomials.Multivariate
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (ArithmeticCircuit (..), Circuit (..))
import ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (getAllVars)
import ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance (ArithmeticCircuitTest (..))

-- This module contains functions for mapping variables in arithmetic circuits.

mapVarWitness :: [Natural] -> (Map Natural a -> Map Natural a)
mapVarWitness vars = mapKeys (mapVar $ Map.fromList $ zip vars [0..])

mapVarArithmeticCircuitTest :: MultiplicativeMonoid a => ArithmeticCircuitTest n a -> ArithmeticCircuitTest n a
mapVarArithmeticCircuitTest (ArithmeticCircuitTest ac wi) =
    let ct = acCircuit ac
        vars = getAllVars ct 
        mappedCircuit = ct
            {
                acSystem  = fromList $ zip [0..] $ mapVarPolynomial (Map.fromList $ zip vars [0..]) <$> elems (acSystem ct),
                -- TODO: the new arithmetic circuit expects the old input variables! We should make this safer.
                acWitness = mapVarWitness vars . acWitness ct
            }
        mappedOutputs = mapVar (Map.fromList $ zip vars [0..]) <$> acOutput ac
        wi' =  mapVarWitness vars wi
    in ArithmeticCircuitTest (ArithmeticCircuit mappedCircuit mappedOutputs) wi'

