module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (
    isZeroC,
    invertC,
) where

import           Control.Monad.State                                 (State, execState)
import           Data.Bool                                           (bool)
import           Data.Map                                            (fromListWith, singleton)
import           Prelude                                             hiding (negate, (+), (*))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate        (monomial, polynomial)

import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal

isZeroC :: (FiniteField a, Eq a, ToBits a) => ArithmeticCircuit a -> ArithmeticCircuit a
isZeroC r = flip execState r $ do
    (setupY, setupZ) <- runInvert r
    setupZ >> setupY

invertC :: (FiniteField a, Eq a, ToBits a) => ArithmeticCircuit a -> ArithmeticCircuit a
invertC r = flip execState r $ do
    (setupY, setupZ) <- runInvert r
    setupY >> setupZ

runInvert :: (FiniteField a, Eq a, ToBits a) => ArithmeticCircuit a -> State (ArithmeticCircuit a) (State (ArithmeticCircuit a) (), State (ArithmeticCircuit a) ())
runInvert r = do
    let x     = acOutput r
        con y = polynomial [monomial one (fromListWith (+) [(x, one), (y, one)])]
    y <- newVariableFromConstraint con
    let con' z = polynomial [monomial one (fromListWith (+) [(x, one), (z, one)]), monomial one (singleton y one), monomial (negate one) (singleton 0 one)]
    return (
        do
        addVariable y
        constraint $ con y
        assignment (bool zero one . (== zero) . eval r ),
        do
        z <- newVariableFromConstraint con'
        addVariable z
        constraint $ con' z
        assignment (invert $ eval r)
      )
