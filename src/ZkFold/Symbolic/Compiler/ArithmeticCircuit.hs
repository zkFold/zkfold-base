{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit (
        ArithmeticCircuit,
        Constraint,
        witnessGenerator,
        -- high-level functions
        optimize,
        desugarRanges,
        -- low-level functions
        eval,
        eval1,
        exec,
        exec1,
        -- information about the system
        acSizeN,
        acSizeM,
        acSystem,
        acValue,
        acPrint,
        -- Variable mapping functions
        mapVarArithmeticCircuit,
        -- Arithmetization type fields
        acWitness,
        acVarOrder,
        acInput,
        acOutput,
        -- Testing functions
        checkCircuit,
        checkClosedCircuit
    ) where

import           Control.Monad.State                                    (execState)
import           Data.Functor.Rep                                       (Representable (..))
import           Data.Map                                               hiding (drop, foldl, foldr, map, null, splitAt,
                                                                         take)
import           Data.Void                                              (absurd)
import           GHC.Generics                                           (U1 (..))
import           Numeric.Natural                                        (Natural)
import           Prelude                                                hiding (Num (..), drop, length, product,
                                                                         splitAt, sum, take, (!!), (^))
import           Test.QuickCheck                                        (Arbitrary, Property, arbitrary, conjoin,
                                                                         property, withMaxSuccess, (===))
import           Text.Pretty.Simple                                     (pPrint)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate           (evalMonomial, evalPolynomial)
import           ZkFold.Prelude                                         (length)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Combinators (desugarRange)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance    ()
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal    (Arithmetic, ArithmeticCircuit (..), Constraint,
                                                                         Var (..), acInput, eval, eval1, exec, exec1,
                                                                         witnessGenerator)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Map

--------------------------------- High-level functions --------------------------------

-- TODO: make this work for different input types.
-- applyArgs :: ArithmeticCircuit a (i :*: j) o -> i a -> ArithmeticCircuit a j o
-- applyArgs r args = (apply args r{acOutput = U1}) {acOutput = fmap _ (acOutput r)}

-- | Optimizes the constraint system.
--
-- TODO: Implement nontrivial optimizations.
optimize :: ArithmeticCircuit a i o -> ArithmeticCircuit a i o
optimize = id

-- | Desugars range constraints into polynomial constraints
desugarRanges :: (Arithmetic a, Ord (Rep i), Representable i) => ArithmeticCircuit a i o -> ArithmeticCircuit a i o
desugarRanges c =
  let r' = flip execState c {acOutput = U1} . traverse (uncurry desugarRange) $ [(NewVar k, v) | (k,v) <- toList (acRange c)]
   in r' { acRange = mempty, acOutput = acOutput c }

----------------------------------- Information -----------------------------------

-- | Calculates the number of constraints in the system.
acSizeN :: ArithmeticCircuit a i o -> Natural
acSizeN = length . acSystem

-- | Calculates the number of variables in the system.
-- The constant `1` is not counted.
acSizeM :: ArithmeticCircuit a i o -> Natural
acSizeM = length . acVarOrder

acValue :: Functor o => ArithmeticCircuit a U1 o -> o a
acValue r = eval r U1

-- | Prints the constraint system, the witness, and the output.
--
-- TODO: Move this elsewhere (?)
-- TODO: Check that all arguments have been applied.
acPrint :: (Show a, Show (o (Var U1)), Show (o a), Functor o) => ArithmeticCircuit a U1 o -> IO ()
acPrint ac = do
    let m = elems (acSystem ac)
        w = witnessGenerator ac U1
        v = acValue ac
        vo = acVarOrder ac
        o = acOutput ac
    putStr "System size: "
    pPrint $ acSizeN ac
    putStr "Variable size: "
    pPrint $ acSizeM ac
    putStr "Matrices: "
    pPrint m
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
    => Scale a a
    => Show a
    => ArithmeticCircuit a U1 n
    -> Property
checkClosedCircuit c = withMaxSuccess 1 $ conjoin [ testPoly p | p <- elems (acSystem c) ]
    where
        w = witnessGenerator c U1
        testPoly p = evalPolynomial evalMonomial varF p === zero
        varF (NewVar v) = w ! v
        varF (InVar v)  = absurd v

checkCircuit
    :: Arbitrary (i a)
    => Arithmetic a
    => Scale a a
    => Show a
    => Representable i
    => ArithmeticCircuit a i n
    -> Property
checkCircuit c = conjoin [ property (testPoly p) | p <- elems (acSystem c) ]
    where
        testPoly p = do
            ins <- arbitrary
            let w = witnessGenerator c ins
                varF (NewVar v) = w ! v
                varF (InVar v)  = index ins v
            return $ evalPolynomial evalMonomial varF p === zero

