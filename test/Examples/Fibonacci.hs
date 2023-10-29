{-# LANGUAGE TypeApplications    #-}

module Examples.Fibonacci (exampleFibonacci) where

import           Prelude                         hiding (Num(..), Eq(..), Bool, (^), (/), (||), not, any)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field  (Zp)
import           ZkFold.Symbolic.Arithmetization  (acSizeM, acSizeN)
import           ZkFold.Symbolic.Compiler         (compile)
import           ZkFold.Symbolic.Data.Bool        (Bool (..))
import           ZkFold.Symbolic.Data.Conditional (bool)
import           ZkFold.Symbolic.Data.Eq          (Eq (..))
import           ZkFold.Symbolic.GroebnerBasis    (fromR1CS, verify)
import           ZkFold.Symbolic.Types            (R, I, SmallField, Symbolic)

-- The Fibonacci index function. If `x` is a Fibonacci number, returns its index (up until `nMax`). Otherwise, returns `0`.
fibonacciIndex :: forall a . Symbolic a => Integer -> a -> a
fibonacciIndex nMax x = foldl (\m k -> bool m (fromConstant @I @a k) (fib k one one == x :: Bool a)) zero [1..nMax]
    where
        fib :: I -> a -> a -> a
        fib 1 x1 _  = x1
        fib n x1 x2 = fib (n - 1) x2 (x1 + x2)

-- The theorem that says that the Fibonacci index function cannot possibly return `nMax + 1`.
fibIndexOutOfRange :: forall a . Symbolic a =>
    Integer -> a -> Bool a
fibIndexOutOfRange nMax x = fibonacciIndex @a nMax x /= fromConstant (nMax + 1)

exampleFibonacci :: IO ()
exampleFibonacci = do
    let nMax = 10

    let r = compile @(Zp SmallField) (fibonacciIndex @R nMax) :: R

    putStrLn "\nStarting Fibonacci test...\n"

    putStrLn "Fibonacci index function"
    putStrLn "R1CS size:"
    putStrLn $ "Number of constraints: " ++ show (acSizeN r)
    putStrLn $ "Number of variables: " ++ show (acSizeM r)

    let Bool r' = compile @(Zp SmallField) (fibIndexOutOfRange @R nMax) :: Bool R

    putStrLn "\nFibonacci index is out of range theorem"
    putStrLn "R1CS size:"
    putStrLn $ "Number of constraints: " ++ show (acSizeN r')
    putStrLn $ "Number of variables: " ++ show (acSizeM r')

    let theorem@(p0, ps) = fromR1CS r'

    putStrLn "\nR1CS polynomials:\n"
    print ps
    putStrLn "\n\"The output equals 1\" polynomial:\n"
    print p0

    putStrLn "\nVerifying the theorem...\n"
    print $ verify theorem