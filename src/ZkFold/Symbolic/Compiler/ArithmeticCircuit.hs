{-# LANGUAGE AllowAmbiguousTypes #-}

module ZkFold.Symbolic.Compiler.ArithmeticCircuit (
        ArithmeticCircuit,
        ArithmeticCircuitTest(..),
        Constraint,
        witnessGenerator,
        -- high-level functions
        applyArgs,
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
        acSizeR,
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

import           Control.Monad                                       (foldM)
import           Control.Monad.State                                 (execState)
import           Data.Map                                            hiding (drop, foldl, foldr, map, null, splitAt,
                                                                      take)
import           GHC.Generics                                        (U1 (..))
import           Numeric.Natural                                     (Natural)
import           Prelude                                             hiding (Num (..), drop, length, product, splitAt,
                                                                      sum, take, (!!), (^))
import           Test.QuickCheck                                     (Arbitrary, Property, conjoin, property, vector,
                                                                      withMaxSuccess, (===))
import           Text.Pretty.Simple                                  (pPrint)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Polynomials.Multivariate        (evalMonomial, evalPolynomial)
import           ZkFold.Prelude                                      (length)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Instance ()
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal (Arithmetic, ArithmeticCircuit (..), Constraint,
                                                                      apply, eval, eval1, exec, exec1, witnessGenerator)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Map
import           ZkFold.Symbolic.Data.Combinators                    (expansion)
import           ZkFold.Symbolic.MonadCircuit                        (MonadCircuit (..))

--------------------------------- High-level functions --------------------------------

-- TODO: make this work for different input types.
applyArgs :: ArithmeticCircuit a f -> [a] -> ArithmeticCircuit a f
applyArgs r args =
    (execState (apply args) r {acOutput = U1}) {acOutput = acOutput r}

-- | Optimizes the constraint system.
--
-- TODO: Implement nontrivial optimizations.
optimize :: ArithmeticCircuit a f -> ArithmeticCircuit a f
optimize = id


desugarRange :: (Arithmetic a, MonadCircuit i a m) => i -> a -> m ()
desugarRange i b
  | b == negate one = return ()
  | otherwise = do
    let bs = binaryExpansion b
    is <- expansion (length bs) i
    case dropWhile ((== one) . fst) (zip bs is) of
      [] -> return ()
      ((_, k0):ds) -> do
        z <- newAssigned (one - ($ k0))
        ge <- foldM (\j (c, k) -> newAssigned $ forceGE j c k) z ds
        constraint (($ ge) - one)
  where forceGE j c k
          | c == zero = ($ j) * (one - ($ k))
          | otherwise = one + ($ k) * (($ j) - one)

-- | Desugars range constraints into polynomial constraints
desugarRanges :: Arithmetic a => ArithmeticCircuit a f -> ArithmeticCircuit a f
desugarRanges c =
  let r' = flip execState c {acOutput = U1} . traverse (uncurry desugarRange) $ toList (acRange c)
   in r' { acRange = mempty, acOutput = acOutput c }

----------------------------------- Information -----------------------------------

-- | Calculates the number of constraints in the system.
acSizeN :: ArithmeticCircuit a f -> Natural
acSizeN = length . acSystem

-- | Calculates the number of variables in the system.
-- The constant `1` is not counted.
acSizeM :: ArithmeticCircuit a f -> Natural
acSizeM = length . acVarOrder

-- | Calculates the number of range lookups in the system.
acSizeR :: ArithmeticCircuit a f -> Natural
acSizeR = length . acRange

acValue :: Functor f => ArithmeticCircuit a f -> f a
acValue r = eval r mempty

-- | Prints the constraint system, the witness, and the output.
--
-- TODO: Move this elsewhere (?)
-- TODO: Check that all arguments have been applied.
acPrint :: (Show a, Show (f Natural), Show (f a), Functor f) => ArithmeticCircuit a f -> IO ()
acPrint ac = do
    let m = elems (acSystem ac)
        i = acInput ac
        w = witnessGenerator ac empty
        v = acValue ac
        vo = acVarOrder ac
        o = acOutput ac
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
    => Scale a a
    => Show a
    => ArithmeticCircuit a n
    -> Property
checkClosedCircuit c = withMaxSuccess 1 $ conjoin [ testPoly p | p <- elems (acSystem c) ]
    where
        w = witnessGenerator c empty
        testPoly p = evalPolynomial evalMonomial (w !) p === zero

checkCircuit
    :: Arbitrary a
    => Arithmetic a
    => Scale a a
    => Show a
    => ArithmeticCircuit a n
    -> Property
checkCircuit c = conjoin [ property (testPoly p) | p <- elems (acSystem c) ]
    where
        testPoly p = do
            ins <- vector . fromIntegral $ length (acInput c)
            let w = witnessGenerator c . fromList $ zip (acInput c) ins
            return $ evalPolynomial evalMonomial (w !) p === zero
