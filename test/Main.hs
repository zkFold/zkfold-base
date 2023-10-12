module Main where

import           Prelude

import           Examples.Fibonacci          (exampleFibonacci)
import           Tests.Arithmetization.Test1 (testArithmetization1)
import           Tests.Arithmetization.Test2 (testArithmetization2)
import           Tests.GroebnerBasis         (testGroebner)
import           Tests.Poly                  (testPoly)

main :: IO ()
main = do
    testGroebner
    testPoly
    testArithmetization1
    testArithmetization2

    exampleFibonacci