{-# LANGUAGE TypeApplications #-}

module Examples.Fibonacci (exampleFibonacci) where

import           Prelude                                     hiding (Bool, Eq (..), Num (..), any, not, (/), (^), (||))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Symbolic.Class                       (Symbolic)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool                   (Bool (..))
import           ZkFold.Symbolic.Data.Conditional            (bool)
import           ZkFold.Symbolic.Data.Eq                     (Eq (..))
import           ZkFold.Symbolic.Data.FieldElement           (FieldElement)

-- | The Fibonacci index function. If `x` is a Fibonacci number, returns its index (up until `nMax`). Otherwise, returns `0`.
fibonacciIndex :: forall c . (Symbolic c, Ring (FieldElement c), Eq (Bool c) (FieldElement c)) => Integer -> FieldElement c -> FieldElement c
fibonacciIndex nMax x = foldl (\m k -> bool m (fromConstant @Integer @(FieldElement c) k) (fib k one one == x :: Bool c)) zero [1..nMax]
    where
        fib :: Integer -> FieldElement c -> FieldElement c -> FieldElement c
        fib 1 x1 _  = x1
        fib n x1 x2 = fib (n - 1) x2 (x1 + x2)

exampleFibonacci :: IO ()
exampleFibonacci = do
    let nMax = 100
        file = "compiled_scripts/fibonacciIndex.json"

    putStrLn "\nExample: Fibonacci index function\n"

    compileIO @(Zp BLS12_381_Scalar) file (fibonacciIndex @(ArithmeticCircuit (Zp BLS12_381_Scalar)) nMax)
