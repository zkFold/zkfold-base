module Main where

import           Prelude
import           System.Directory       (createDirectoryIfMissing)

import           Examples.Eq            (exampleEq)
import           Examples.Fibonacci     (exampleFibonacci)
import           Examples.LEQ           (exampleLEQ)
import           Examples.MiMCHash      (exampleMiMC)
import           Examples.ReverseList   (exampleReverseList)

main :: IO ()
main = do
    createDirectoryIfMissing True "compiled_scripts"
    
    exampleReverseList
    exampleEq
    exampleFibonacci
    exampleMiMC
    exampleLEQ
    