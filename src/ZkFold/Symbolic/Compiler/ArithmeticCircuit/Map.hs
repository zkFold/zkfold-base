{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Map (
        mapVarArithmeticCircuit,
        ArithmeticCircuitTest(..)
    ) where

import           Data.Map                                               hiding (drop, foldl, foldr, fromList, map, null,
                                                                         splitAt, take, toList)
import qualified Data.Map                                               as Map
import           GHC.Generics                                           (Par1)
import           GHC.IsList                                             (IsList (..))
import           GHC.Natural                                            (naturalToInteger)
import           GHC.Num                                                (integerToInt)
import           Numeric.Natural                                        (Natural)
import           Prelude                                                hiding (Num (..), drop, length, product,
                                                                         splitAt, sum, take, (!!), (^))
import           Test.QuickCheck                                        (Arbitrary (arbitrary), Gen, vector)

import           ZkFold.Base.Algebra.Basic.Class                        (MultiplicativeMonoid (..))
import           ZkFold.Base.Algebra.Polynomials.Multivariate
import           ZkFold.Prelude                                         (length)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (getAllVars)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal    (Arithmetic, ArithmeticCircuit (..),
                                                                         Circuit (..), inputVariables)

-- This module contains functions for mapping variables in arithmetic circuits.

data ArithmeticCircuitTest a f = ArithmeticCircuitTest
    {
        arithmeticCircuit :: ArithmeticCircuit a f
        , witnessInput    :: Map.Map Natural a
    }

instance (Show (ArithmeticCircuit a f), Show a) => Show (ArithmeticCircuitTest a f) where
    show (ArithmeticCircuitTest ac wi) = show ac ++ ",\nwitnessInput: " ++ show wi

instance (Arithmetic a, Arbitrary a, Arbitrary (ArithmeticCircuit a Par1)) => Arbitrary (ArithmeticCircuitTest a Par1) where
    arbitrary :: Gen (ArithmeticCircuitTest a Par1)
    arbitrary = do
        ac <- arbitrary
        let keysAC = inputVariables ac
        values <- vector . integerToInt . naturalToInteger . length  $ keysAC
        let wi = fromList $ zip keysAC values
        return ArithmeticCircuitTest {
            arithmeticCircuit = ac
            , witnessInput = wi
            }

mapVarArithmeticCircuit :: (MultiplicativeMonoid a, Functor f) => ArithmeticCircuitTest a f -> ArithmeticCircuitTest a f
mapVarArithmeticCircuit (ArithmeticCircuitTest ac wi) =
    let ct = acCircuit ac
        vars = getAllVars ct
        forward = Map.fromAscList $ zip vars [0..]
        backward = Map.fromAscList $ zip [0..] vars
        mappedCircuit = ct
            {
                acSystem  = fromList $ zip [0..] $ mapVarPolynomial forward <$> elems (acSystem ct),
                -- TODO: the new arithmetic circuit expects the old input variables! We should make this safer.
                acWitness = (`Map.compose` backward) $ (. (`Map.compose` forward)) <$> acWitness ct
            }
        mappedOutputs = mapVar forward <$> acOutput ac
        wi' = wi `Map.compose` backward
    in ArithmeticCircuitTest (ArithmeticCircuit mappedCircuit mappedOutputs) wi'
