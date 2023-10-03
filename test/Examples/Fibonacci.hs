{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Examples.Fibonacci (exampleFibonacci) where

import           Data.List                                   (find)
import           Data.Map                                    (singleton)
import           Prelude                                     hiding ((||), not, Num(..), Eq(..), (^), (/), any)

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Algebra.Basic.Field
import           ZkFold.Crypto.Protocol.Arithmetization.R1CS
import           ZkFold.Crypto.Data.Arithmetization          (Arithmetization(..))
import           ZkFold.Crypto.Data.Bool                     (GeneralizedBoolean(..), SymbolicBool (..))
import           ZkFold.Crypto.Data.Conditional              (GeneralizedConditional, bool)
import           ZkFold.Crypto.Data.Eq                       (GeneralizedEq (..))

import           Tests.Utility.Types                         (SmallField)

type R = R1CS (Zp SmallField) (Zp SmallField) Integer
type I = Integer

fibonacciIndex :: forall a b . (FiniteField a, GeneralizedEq b a, GeneralizedConditional b a, FromConstant I a) => a -> a
fibonacciIndex x = foldl (\m k -> bool m (fromConstant @I @a k) (fib k one one == x :: b)) zero [1..10]
    where
        fib :: I -> a -> a -> a
        fib 1 x1 _  = x1
        fib n x1 x2 = fib (n - 1) x2 (x1 + x2)

fibIndexIsNotFive :: forall a b . (FiniteField a, GeneralizedEq b a, GeneralizedConditional b a, FromConstant I a) => a -> b
fibIndexIsNotFive x = (fibonacciIndex @a @b x /= fromConstant @I @a 5 :: b) || (x == fromConstant @I @a 5 :: b)

testResult :: R -> Zp SmallField -> Bool
testResult r x =
    let v = eval @R @R r $ singleton one x
    in v == fibonacciIndex @(Zp SmallField) @Bool x

exampleFibonacci :: IO ()
exampleFibonacci = do
    putStrLn "\nStarting Fibonacci test...\n"

    let r = compile (fibonacciIndex @R @(SymbolicBool R))
    putStrLn "\nR1CS size:"
    putStrLn $ "Number of constraints: " ++ show (r1csSizeN r)
    putStrLn $ "Number of variables: " ++ show (r1csSizeM r)

    let m   = map toZp [1..order @SmallField - 1]
        res = zip m $ map (testResult r) m
    case find (not . snd) res of
        Nothing     -> putStrLn "Success!"
        Just (x, _) -> do
            putStrLn $ "Failure at " ++ show x ++ "!"

            print $ eval @R @R r $ singleton one x
            print $ fibonacciIndex @(Zp SmallField) @Bool x
            