module Main where

import           Prelude
import           Test.Hspec            (hspec)

import           Tests.Arithmetization (specArithmetization)

main :: IO ()
main = hspec $ do
    specArithmetization
    -- specGroebner