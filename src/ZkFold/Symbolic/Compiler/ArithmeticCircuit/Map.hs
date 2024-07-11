{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Map (
        mapVarArithmeticCircuit,
        mapVarWitness,
        ArithmeticCircuitTest(..)
    ) where

import           Data.Map                                               hiding (drop, foldl, foldr, fromList, map, null,
                                                                         splitAt, take, toList)
import qualified Data.Map                                               as Map
import           GHC.IsList                                             (IsList (..))
import           Numeric.Natural                                        (Natural)
import           Prelude                                                hiding (Num (..), drop, length, product,
                                                                         splitAt, sum, take, (!!), (^))

import           ZkFold.Base.Algebra.Basic.Class                        (MultiplicativeMonoid (..))
import           ZkFold.Base.Algebra.Polynomials.Multivariate
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (getAllVars)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal    (ArithmeticCircuit (..), Circuit (..), Arithmetic, inputVariables)
import Test.QuickCheck (Arbitrary (arbitrary), Gen, vector)
import GHC.Natural (naturalToInteger)
import           GHC.Num                                                   (integerToInt)
import           ZkFold.Prelude                                            (length)

-- This module contains functions for mapping variables in arithmetic circuits.

data ArithmeticCircuitTest n a = ArithmeticCircuitTest
    {
        arithmeticCircuit :: ArithmeticCircuit n a
        , witnessInput    :: Map.Map Natural a
    }

instance (Show (ArithmeticCircuit n a), Show a) => Show (ArithmeticCircuitTest n a) where
    show (ArithmeticCircuitTest ac wi) = show ac ++ ",\nwitnessInput: " ++ show wi

instance (Arithmetic a, Arbitrary a, Arbitrary (ArithmeticCircuit 1 a)) => Arbitrary (ArithmeticCircuitTest 1 a) where
    arbitrary :: Gen (ArithmeticCircuitTest 1 a)
    arbitrary = do
        ac <- arbitrary
        let keysAC = inputVariables ac
        values <- vector . integerToInt . naturalToInteger . length  $ keysAC
        let wi = fromList $ zip keysAC values
        return ArithmeticCircuitTest {
            arithmeticCircuit = ac
            , witnessInput = wi
            }

mapVarWitness :: [Natural] -> (Map Natural a -> Map Natural a)
mapVarWitness vars = mapKeys (mapVar $ Map.fromList $ zip vars [0..])

mapVarArithmeticCircuit :: MultiplicativeMonoid a => ArithmeticCircuitTest n a -> ArithmeticCircuitTest n a
mapVarArithmeticCircuit (ArithmeticCircuitTest ac wi) =
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

