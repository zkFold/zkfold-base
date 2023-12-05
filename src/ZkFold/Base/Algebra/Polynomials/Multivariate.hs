module ZkFold.Base.Algebra.Polynomials.Multivariate (
    Variable,
    Monomial,
    Polynomial,
    variable,
    monomial,
    polynomial,
    evalMultivariate,
    variableList
    ) where

import           Data.Map                        (Map, toList, keys)
import           Prelude                         hiding (sum, (^), product, Num(..), (!!), length, replicate)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Prelude                  ((!))

import           ZkFold.Base.Algebra.Polynomials.Multivariate.Internal hiding (scale)

type Variable a = Var a Integer

variable :: Integer -> Variable a
variable = Var

type Monomial a = Monom a Integer

monomial :: a -> Map Integer (Variable a) -> Monomial a
monomial = M

type Polynomial a = Polynom a Integer

polynomial :: (FiniteField a, Eq a) => [Monomial a] -> Polynomial a
polynomial = sum . map (\m -> P [m]) . filter (not . zeroM)

evalMonomial :: (Eq a, ToBits a, FiniteField b) =>Monom a Integer -> Map Integer b -> b
evalMonomial (M c m) xs = scale c $ product (map (\(i, Var j) -> (xs ! i)^j) (toList m))

evalMultivariate :: (Eq a, ToBits a, FiniteField b) => Polynomial a -> Map Integer b -> b
evalMultivariate (P []) _ = zero
evalMultivariate (P (m:ms)) xs = evalMultivariate (P ms) xs + evalMonomial m xs

variableList :: Polynomial a -> [Integer]
variableList (P []) = []
variableList (P (m:ms)) =
    let variableList' (M _ as) = keys as
    in variableList' m ++ variableList (P ms)