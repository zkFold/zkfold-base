{-# LANGUAGE TypeApplications #-}

module Examples.Fibonacci (exampleFibonacci) where

import           Prelude                                     hiding (Bool, Eq (..), Num (..), any, not, (/), (^), (||))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool                   (Bool (..))
import           ZkFold.Symbolic.Data.Conditional            (Conditional, bool)
import           ZkFold.Symbolic.Data.Eq                     (Eq (..))

-- | The Fibonacci index function. If `x` is a Fibonacci number, returns its index (up until `nMax`). Otherwise, returns `0`.
fibonacciIndex :: forall c . (Ring (c 1), Eq (Bool c) (c 1), Conditional (Bool c) (c 1)) => Integer -> c 1 -> c 1
fibonacciIndex nMax x = foldl (\m k -> bool m (fromConstant @Integer @(c 1) k) (fib k one one == x :: Bool c)) zero [1..nMax]
    where
        fib :: Integer -> c 1 -> c 1 -> c 1
        fib 1 x1 _  = x1
        fib n x1 x2 = fib (n - 1) x2 (x1 + x2)

exampleFibonacci :: IO ()
exampleFibonacci = do
    let nMax = 100
        file = "compiled_scripts/fibonacciIndex.json"

    putStrLn "\nExample: Fibonacci index function\n"

    compileIO @(Zp BLS12_381_Scalar) file (fibonacciIndex @(ArithmeticCircuit (Zp BLS12_381_Scalar)) nMax)
