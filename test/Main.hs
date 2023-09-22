module Main where

import           Prelude

import           Tests.Arithmetization (testArithmetization)

main :: IO ()
main = do
    testArithmetization