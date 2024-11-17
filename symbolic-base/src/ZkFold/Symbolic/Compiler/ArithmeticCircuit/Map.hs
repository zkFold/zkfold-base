{-# LANGUAGE AllowAmbiguousTypes  #-}
{-# LANGUAGE UndecidableInstances #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Map (
        mapVarArithmeticCircuit,
        ArithmeticCircuitTest(..)
    ) where

import           Data.Functor                                        ((<&>))
import           Data.Functor.Rep                                    (Representable (..))
import           Data.Map                                            hiding (drop, foldl, foldr, fromList, map, null,
                                                                      splitAt, take, toList)
import qualified Data.Map                                            as Map
import qualified Data.Set                                            as Set
import           GHC.IsList                                          (IsList (..))
import           Numeric.Natural                                     (Natural)
import           Prelude                                             hiding (Num (..), drop, length, product, splitAt,
                                                                      sum, take, (!!), (^))
import           Test.QuickCheck                                     (Arbitrary (arbitrary), Gen)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate
import           ZkFold.Base.Data.ByteString                         (toByteString)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (Arithmetic, ArithmeticCircuit (..), SysVar (..),
                                                                      Var (..), VarField, getAllVars)

-- This module contains functions for mapping variables in arithmetic circuits.

data ArithmeticCircuitTest a p i o = ArithmeticCircuitTest
    {
        arithmeticCircuit :: ArithmeticCircuit a p i o
        , witnessInput    :: i a
    }

instance (Show (ArithmeticCircuit a p i o), Show a, Show (i a)) => Show (ArithmeticCircuitTest a p i o) where
    show (ArithmeticCircuitTest ac wi) = show ac ++ ",\nwitnessInput: " ++ show wi

instance (Arithmetic a, Arbitrary (i a), Arbitrary (ArithmeticCircuit a p i f), Representable i) => Arbitrary (ArithmeticCircuitTest a p i f) where
    arbitrary :: Gen (ArithmeticCircuitTest a p i f)
    arbitrary = do
        ac <- arbitrary
        wi <- arbitrary
        return ArithmeticCircuitTest {
            arithmeticCircuit = ac
            , witnessInput = wi
            }

mapVarArithmeticCircuit :: (Field a, Eq a, Functor o, Ord (Rep i), Representable i, Foldable i) => ArithmeticCircuitTest a p i o -> ArithmeticCircuitTest a p i o
mapVarArithmeticCircuit (ArithmeticCircuitTest ac wi) =
    let vars = [v | NewVar v <- getAllVars ac]
        asc = [ toByteString @VarField (fromConstant @Natural x) | x <- [0..] ]
        forward = Map.fromAscList $ zip vars asc
        backward = Map.fromAscList $ zip asc vars
        varF (InVar v)  = InVar v
        varF (NewVar v) = NewVar (forward ! v)
        mappedCircuit = ArithmeticCircuit
          { acRange   = Set.map varF <$> acRange ac
          , acSystem  = fromList $ zip asc $ evalPolynomial evalMonomial (var . varF) <$> elems (acSystem ac)
          , acWitness = (`Map.compose` backward) $ fmap varF <$> acWitness ac
          , acOutput  = acOutput ac <&> \case
              SysVar v -> SysVar (varF v)
              ConstVar c -> ConstVar c
          }
    in ArithmeticCircuitTest mappedCircuit wi
