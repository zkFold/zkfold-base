{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit (
        ArithmeticCircuit,
        Constraint,

        withOutputs,
        constraintSystem,
        inputVariables,
        witnessGenerator,
        varOrder,
        -- high-level functions
        applyArgs,
        optimize,
        -- low-level functions
        eval,
        eval1,
        exec,
        exec1,
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
import           Data.Map                                            hiding (drop, foldl, foldr, map, null, splitAt,
                                                                      take)
import           Numeric.Natural                                     (Natural)
import           Prelude                                             hiding (Num (..), drop, length, product, splitAt,
                                                                      sum, take, (!!), (^))
import           Test.QuickCheck                                     (Arbitrary, Property, conjoin, property, vector,
                                                                      withMaxSuccess, (===))
import           Text.Pretty.Simple                                  (pPrint)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate        (evalMonomial, evalPolynomial)
import           ZkFold.Base.Data.Vector                             (Vector)
import           ZkFold.Prelude                                      (length)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance ()
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (Arithmetic, ArithmeticCircuit (..), Circuit (..),
                                                                      Constraint, apply, constraintSystem, eval, eval1,
                                                                      exec, exec1, forceZero, inputVariables, varOrder,
                                                                      withOutputs, witnessGenerator)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Map

--------------------------------- High-level functions --------------------------------

-- TODO: make this work for different input types.
applyArgs :: forall a n . ArithmeticCircuit n a -> [a] -> ArithmeticCircuit n a
applyArgs r args = r { acCircuit = execState (apply args) (acCircuit r) }

-- | Optimizes the constraint system.
--
-- TODO: Implement nontrivial optimizations.
optimize :: forall a n . ArithmeticCircuit n a -> ArithmeticCircuit n a
optimize = id

----------------------------------- Information -----------------------------------

-- | Calculates the number of constraints in the system.
acSizeN :: forall a n . ArithmeticCircuit n a -> Natural
acSizeN = length . acSystem . acCircuit

-- | Calculates the number of variables in the system.
-- The constant `1` is not counted.
acSizeM :: forall a n . ArithmeticCircuit n a -> Natural
acSizeM = length . acVarOrder . acCircuit

acValue :: forall a n . ArithmeticCircuit n a -> Vector n a
acValue r = eval r mempty

-- | Prints the constraint system, the witness, and the output.
--
-- TODO: Move this elsewhere (?)
-- TODO: Check that all arguments have been applied.
acPrint :: forall a n . Show a => ArithmeticCircuit n a -> IO ()
acPrint ac@(ArithmeticCircuit r o) = do
    let m = elems (acSystem r)
        i = acInput r
        w = acWitness r empty
        v = acValue ac
        vo = acVarOrder r
    putStr "System size: "
    pPrint $ acSizeN ac
    putStr "Variable size: "
    pPrint $ acSizeM ac
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

checkClosedCircuit
    :: forall a n
     . Arithmetic a
    => FromConstant a a
    => Scale a a
    => Show a
    => ArithmeticCircuit n a
    -> Property
checkClosedCircuit (ArithmeticCircuit r _) = withMaxSuccess 1 $ conjoin [ testPoly p | p <- elems (acSystem r) ]
    where
        w = acWitness r empty
        testPoly p = evalPolynomial evalMonomial (w !) p === zero

checkCircuit
    :: forall a n
     . Arbitrary a
    => Arithmetic a
    => FromConstant a a
    => Scale a a
    => Show a
    => ArithmeticCircuit n a
    -> Property
checkCircuit (ArithmeticCircuit r _) = conjoin [ property (testPoly p) | p <- elems (acSystem r) ]
    where
        testPoly p = do
            ins <- vector . fromIntegral $ length (acInput r)
            let w = acWitness r . fromList $ zip (acInput r) ins
            return $ evalPolynomial evalMonomial (w !) p === zero
