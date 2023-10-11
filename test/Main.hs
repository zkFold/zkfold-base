module Main where

import           Prelude

import           Examples.Fibonacci          (exampleFibonacci)
import           Tests.Arithmetization.Test1 (testArithmetization1)
import           Tests.Arithmetization.Test2 (testArithmetization2)
import           Tests.GroebnerBasis         (testGroebner)

main :: IO ()
main = do
    testGroebner
    testArithmetization1
    testArithmetization2

    exampleFibonacci