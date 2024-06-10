{-# LANGUAGE TypeApplications #-}

module Examples.Fibonacci (exampleFibonacci) where

import           GHC.Generics                                (Par1(Par1))
import           Prelude                                     hiding (Bool, Eq (..), Num (..), any, not, (/), (^), (||))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool                   (Bool (..), Eq (..), bool)
import           ZkFold.Symbolic.Types                       (Symbolic)

-- | The Fibonacci index function. If `x` is a Fibonacci number, returns its index (up until `nMax`). Otherwise, returns `0`.
fibonacciIndex :: forall a . Symbolic a => Integer -> Par1 a -> Par1 a
fibonacciIndex nMax x = foldl (\m k -> bool m (Par1 (fromConstant @Integer @a k)) (Par1 (fib k one one) == x :: Bool a)) (Par1 zero) [1..nMax]
    where
        fib :: Integer -> a -> a -> a
        fib 1 x1 _  = x1
        fib n x1 x2 = fib (n - 1) x2 (x1 + x2)

exampleFibonacci :: IO ()
exampleFibonacci = do
    let nMax = 100
        file = "compiled_scripts/fibonacciIndex.json"

    putStrLn "\nExample: Fibonacci index function\n"

    compileIO @(Zp BLS12_381_Scalar) file (fibonacciIndex @(ArithmeticCircuit (Zp BLS12_381_Scalar)) nMax)
