module ZkFold.Base.Algebra.Polynomials.Multivariate (
    Variable,
    Monomial,
    Polynomial,
    variable,
    monomial,
    getPowers,
    polynomial,
    getMonomials,
    evalMultivariate,
    variableList
    ) where

import           Data.Map                        (Map, toList, keys)
import           Prelude                         hiding (sum, (^), product, Num(..), (!!), length, replicate)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Prelude                  ((!))

import           ZkFold.Base.Algebra.Polynomials.Multivariate.Internal

type Variable a = Var a Integer

variable :: Integer -> Variable a
variable = Var

type Monomial a = Monom a Integer

monomial :: a -> Map Integer (Variable a) -> Monomial a
monomial = M

getPowers :: Monomial a -> Map Integer Integer
getPowers (M _ as) = fmap getPower as

type Polynomial a = Polynom a Integer

polynomial :: (FiniteField a, Eq a) => [Monomial a] -> Polynomial a
polynomial = sum . map (\m -> P [m]) . filter (not . zeroM)

getMonomials :: Polynomial a -> [Monomial a]
getMonomials (P ms) = ms

evalMonomial :: Algebra b a => Monom a Integer -> Map Integer b -> b
evalMonomial (M c m) xs = scale c $ product (map (\(i, Var j) -> (xs ! i)^j) (toList m))

evalMultivariate :: Algebra b a => Polynomial a -> Map Integer b -> b
evalMultivariate (P []) _ = zero
evalMultivariate (P (m:ms)) xs = evalMultivariate (P ms) xs + evalMonomial m xs

variableList :: Polynomial a -> [Integer]
variableList (P []) = []
variableList (P (m:ms)) =
    let variableList' (M _ as) = keys as
    in variableList' m ++ variableList (P ms)
