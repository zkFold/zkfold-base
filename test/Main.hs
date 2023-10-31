module Main where

import           Prelude

import           Examples.Fibonacci          (exampleFibonacci)
import           Examples.LEQ                (exampleLEQ)
import           Examples.MiMCHash           (exampleMiMC)
import           Tests.Arithmetization       (testArithmetization)
import           Tests.GroebnerBasis         (testGroebner)

main :: IO ()
main = do
    testGroebner
    testArithmetization

    exampleFibonacci
    exampleMiMC
    exampleLEQ