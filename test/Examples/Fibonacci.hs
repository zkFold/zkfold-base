{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Examples.Fibonacci (exampleFibonacci) where

import           Prelude                                     hiding ((||), not, Num(..), Eq(..), (^), (/), any)

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis (fromR1CS, verify)
import           ZkFold.Crypto.Protocol.Arithmetization.R1CS
import           ZkFold.Crypto.Data.Arithmetization          (Arithmetization(..))
import           ZkFold.Crypto.Data.Bool                     (SymbolicBool (..))
import           ZkFold.Crypto.Data.Conditional              (GeneralizedConditional, bool)
import           ZkFold.Crypto.Data.Eq                       (GeneralizedEq (..))

import           Tests.Utility.Types                         (R, I)

-- The Fibonacci index function. If `x` is a Fibonacci number, returns its index (up until `nMax`). Otherwise, returns `0`.
fibonacciIndex :: forall a b . (FiniteField a, GeneralizedEq b a, GeneralizedConditional b a, FromConstant I a) => Integer -> a -> a
fibonacciIndex nMax x = foldl (\m k -> bool m (fromConstant @I @a k) (fib k one one == x :: b)) zero [1..nMax]
    where
        fib :: I -> a -> a -> a
        fib 1 x1 _  = x1
        fib n x1 x2 = fib (n - 1) x2 (x1 + x2)

-- The theorem that says that the Fibonacci index function cannot possibly return `nMax + 1`.
fibIndexOutOfRange :: forall a b . (FiniteField a, GeneralizedEq b a, GeneralizedConditional b a, FromConstant I a) => Integer -> a -> b
fibIndexOutOfRange nMax x = fibonacciIndex @a @b nMax x /= fromConstant @I @a (nMax + 1) :: b

exampleFibonacci :: IO ()
exampleFibonacci = do
    let nMax = 5

    let r = compile @R (fibonacciIndex @R @(SymbolicBool R) nMax)

    putStrLn "\nStarting Fibonacci test...\n"

    putStrLn "Fibonacci index function"
    putStrLn "R1CS size:"
    putStrLn $ "Number of constraints: " ++ show (r1csSizeN r)
    putStrLn $ "Number of variables: " ++ show (r1csSizeM r)

    let r' = compile (fibIndexOutOfRange @R @(SymbolicBool R) nMax) :: R

    putStrLn "\nFibonacci index is out of range theorem"
    putStrLn "R1CS size:"
    putStrLn $ "Number of constraints: " ++ show (r1csSizeN r')
    putStrLn $ "Number of variables: " ++ show (r1csSizeM r')

    let theorem@(p0, ps) = fromR1CS r'

    putStrLn "\nR1CS polynomials:\n"
    print ps
    putStrLn "\n\"The output equals 1\" polynomial:\n"
    print p0

    putStrLn "\nVerifying the theorem...\n"
    print $ verify theorem