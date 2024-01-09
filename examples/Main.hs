module Main where

import           Prelude
import           System.Directory            (createDirectoryIfMissing)

import           Examples.Eq                 (exampleEq)
import           Examples.Fibonacci          (exampleFibonacci)
import           Examples.LEQ                (exampleLEQ)
import           Examples.MiMCHash           (exampleMiMC)

main :: IO ()
main = do
    createDirectoryIfMissing True "compiled_scripts"
    
    exampleEq
    exampleFibonacci
    exampleMiMC
    exampleLEQ