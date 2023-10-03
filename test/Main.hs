module Main where

import           Prelude

import           Tests.Arithmetization (testArithmetization)
import           Tests.GroebnerBasis   (testGroebner)

import           Examples.Fibonacci    (exampleFibonacci)

main :: IO ()
main = do
    testGroebner
    testArithmetization

    exampleFibonacci