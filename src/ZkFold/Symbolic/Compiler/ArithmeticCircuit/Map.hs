{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Map (
        mapVarArithmeticCircuit,
        ArithmeticCircuitTest(..)
    ) where

import           Data.Functor.Rep                                    (Representable (..))
import           Data.Map                                            hiding (drop, foldl, foldr, fromList, map, null,
                                                                      splitAt, take, toList)
import qualified Data.Map                                            as Map
import           GHC.Generics                                        (Par1)
import           GHC.IsList                                          (IsList (..))
import           Prelude                                             hiding (Num (..), drop, length, product, splitAt,
                                                                      sum, take, (!!), (^))
import           Test.QuickCheck                                     (Arbitrary (arbitrary), Gen)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (Arithmetic, ArithmeticCircuit (..), Var (..),
                                                                      getAllVars)

-- This module contains functions for mapping variables in arithmetic circuits.

data ArithmeticCircuitTest a i o = ArithmeticCircuitTest
    {
        arithmeticCircuit :: ArithmeticCircuit a i o
        , witnessInput    :: i a
    }

instance (Show (ArithmeticCircuit a i o), Show a, Show (i a)) => Show (ArithmeticCircuitTest a i o) where
    show (ArithmeticCircuitTest ac wi) = show ac ++ ",\nwitnessInput: " ++ show wi

instance (Arithmetic a, Arbitrary (i a), Arbitrary (ArithmeticCircuit a i Par1), Representable i) => Arbitrary (ArithmeticCircuitTest a i Par1) where
    arbitrary :: Gen (ArithmeticCircuitTest a i Par1)
    arbitrary = do
        ac <- arbitrary
        wi <- arbitrary
        return ArithmeticCircuitTest {
            arithmeticCircuit = ac
            , witnessInput = wi
            }

mapVarArithmeticCircuit :: (Field a, Scale a a, Eq a, Functor o, Ord (Rep i), Representable i, Foldable i) => ArithmeticCircuitTest a i o -> ArithmeticCircuitTest a i o
mapVarArithmeticCircuit (ArithmeticCircuitTest ac wi) =
    let vars = [v | NewVar v <- getAllVars ac]
        forward = Map.fromAscList $ zip vars [0..]
        backward = Map.fromAscList $ zip [0..] vars
        varF (InVar v)  = InVar v
        varF (NewVar v) = NewVar (forward ! v)
        mappedCircuit = ac
            {
                acSystem  = fromList $ zip [0..] $ evalPolynomial evalMonomial (var . varF) <$> elems (acSystem ac),
                -- TODO: the new arithmetic circuit expects the old input variables! We should make this safer.
                acWitness = (`Map.compose` backward) $ acWitness ac
            }
        mappedOutputs = varF <$> acOutput ac
    in ArithmeticCircuitTest (mappedCircuit {acOutput = mappedOutputs}) wi
