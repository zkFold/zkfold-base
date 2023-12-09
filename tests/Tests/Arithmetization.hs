module Tests.Arithmetization (specArithmetization) where

import           Prelude
import           Test.Hspec                  (Spec, describe)

import           Tests.Arithmetization.Test1 (specArithmetization1)
import           Tests.Arithmetization.Test2 (specArithmetization2)
import           Tests.Arithmetization.Test3 (specArithmetization3)

specArithmetization :: Spec
specArithmetization = do
    describe "Arithmetization specification" $ do
        specArithmetization1
        specArithmetization2
        specArithmetization3