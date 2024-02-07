module ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (
    isZeroC,
    invertC,
    mappendC,
    plusMultC,
) where

import           Control.Monad.State                                 (State, execState)
import           Data.Bool                                           (bool)
import           Data.List                                           (nub)
import           Data.Map                                            (fromListWith, singleton, union)
import           Prelude                                             hiding (negate, (+), (*))
import qualified Prelude                                             as Haskell
import           System.Random                                       (mkStdGen, uniform)

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

mappendC :: ArithmeticCircuit a -> ArithmeticCircuit a -> ArithmeticCircuit a
mappendC r1 r2 = ArithmeticCircuit
    {
        acSystem   = acSystem r1 `union` acSystem r2,
        -- NOTE: is it possible that we get a wrong argument order when doing `apply` because of this concatenation?
        -- We need a way to ensure the correct order no matter how `(<>)` is used.
        acInput    = nub $ acInput r1 ++ acInput r2,
        acWitness  = \w -> acWitness r1 w `union` acWitness r2 w,
        acOutput   = max (acOutput r1) (acOutput r2),
        acVarOrder = acVarOrder r1 `union` acVarOrder r2,
        acRNG      = mkStdGen $ fst (uniform (acRNG r1)) Haskell.* fst (uniform (acRNG r2))
    }

plusMultC :: (FiniteField a, Eq a, ToBits a) => ArithmeticCircuit a -> ArithmeticCircuit a -> ArithmeticCircuit a -> ArithmeticCircuit a
-- ^ @plusMult a b c@ computes @a + b * c@ in one PLONK constraint.
plusMultC a b c = flip execState (a `mappendC` b `mappendC` c) $ do
    let x     = acOutput a
        y     = acOutput b
        z     = acOutput c
        con w = polynomial [
                    monomial one (singleton x one),
                    monomial one (fromListWith (+) [(y, one), (z, one)]),
                    monomial (negate one) (singleton w one)
                ]
    w <- newVariableFromConstraint con
    addVariable w
    constraint (con w)
    assignment (eval a + eval b * eval c)
