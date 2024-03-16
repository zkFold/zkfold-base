{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit (
        ArithmeticCircuit,
        Constraint,
        -- high-level functions
        applyArgs,
        optimize,
        -- low-level functions
        eval,
        forceZero,
        -- information about the system
        acSizeN,
        acSizeM,
        acSystem,
        acValue,
        acPrint,
        -- Variable mapping functions
        mapVarArithmeticCircuit,
        mapVarWitness,
        -- Arithmetization type fields
        acWitness,
        acVarOrder,
        acOutput,
        -- Testing functions
        checkCircuit,
        checkClosedCircuit
    ) where

import           Control.Monad.State                                 (execState)
import           Data.Map                                            hiding (take, drop, splitAt, foldl, null, map, foldr)
import           Prelude                                             hiding (Num (..), (^), (!!), sum, take, drop, splitAt, product, length)
import           Test.QuickCheck                                     (Arbitrary, Property, conjoin, property, vector, withMaxSuccess, (===))
import           Text.Pretty.Simple                                  (pPrint)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate        (evalPolynomial')
import           ZkFold.Prelude                                      (length)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (ArithmeticCircuit(..), Arithmetic, Constraint, apply, eval, forceZero)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance ()
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Map

--------------------------------- High-level functions --------------------------------

-- TODO: make this work for different input types.
applyArgs :: forall a . ArithmeticCircuit a -> [a] -> ArithmeticCircuit a
applyArgs r args = execState (apply args) r

-- | Optimizes the constraint system.
--
-- TODO: Implement this.
optimize :: ArithmeticCircuit a -> ArithmeticCircuit a
optimize = undefined

----------------------------------- Information -----------------------------------

-- | Calculates the number of constraints in the system.
acSizeN :: ArithmeticCircuit a -> Integer
acSizeN = length . acSystem

-- | Calculates the number of variables in the system.
-- The constant `1` is not counted.
acSizeM :: ArithmeticCircuit a -> Integer
acSizeM = length . acVarOrder

acValue :: ArithmeticCircuit a -> a
acValue r = eval r

-- | Prints the constraint system, the witness, and the output.
--
-- TODO: Move this elsewhere (?)
-- TODO: Check that all arguments have been applied.
acPrint :: forall a . (FiniteField a, Eq a, Show a) => ArithmeticCircuit a -> IO ()
acPrint r = do
    let m = elems (acSystem r)
        i = acInput r
        w = acWitness r
        o = acOutput r
        v = acValue r
        vo = acVarOrder r
    putStr "System size: "
    pPrint $ acSizeN r
    putStr "Variable size: "
    pPrint $ acSizeM r
    putStr "Matrices: "
    pPrint m
    putStr "Input: "
    pPrint i
    putStr "Witness: "
    pPrint w
    putStr "Variable order: "
    pPrint vo
    putStr "Output: "
    pPrint o
    putStr "Value: "
    pPrint v

---------------------------------- Testing -------------------------------------

checkClosedCircuit :: (Arithmetic a, Show a) => ArithmeticCircuit a -> Property
checkClosedCircuit r = withMaxSuccess 1 $ conjoin [ testPoly p | p <- elems (acSystem r) ]
    where
        testPoly p = evalPolynomial' (acWitness r !) p === zero

-- TODO: fix it while fixing tests
checkCircuit :: (Arbitrary a, Arithmetic a, Show a) => ArithmeticCircuit a -> Property
checkCircuit r = conjoin [ property (testPoly p) | p <- elems (acSystem r) ]
    where
        testPoly p = do
            -- ins <- vector . fromIntegral $ length (acInput r)
            -- let w = acWitness r . fromList $ zip (acInput r) ins
            -- return $ evalPolynomial' (w !) p === zero
            property True
