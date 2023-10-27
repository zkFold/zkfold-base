module Tests.Arithmetization (testArithmetization) where

import           Prelude

import           Tests.Arithmetization.Test1 (testArithmetization1)
import           Tests.Arithmetization.Test2 (testArithmetization2)
import           Tests.Arithmetization.Test3 (testArithmetization3)

testArithmetization :: IO ()
testArithmetization = do
    testArithmetization1
    testArithmetization2
    testArithmetization3