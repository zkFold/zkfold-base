module Main where

import           Prelude

import           Examples.Fibonacci          (exampleFibonacci)
import           Examples.LEQ                (exampleLEQ)
import           Examples.MiMCHash           (exampleMiMC)

main :: IO ()
main = do
    exampleFibonacci
    exampleMiMC
    exampleLEQ