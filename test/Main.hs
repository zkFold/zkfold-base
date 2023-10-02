module Main where

import           Prelude

import           Tests.Arithmetization (testArithmetization)
import           Tests.GroebnerBasis   (testGroebner)

main :: IO ()
main = do
    testGroebner
    testArithmetization