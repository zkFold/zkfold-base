{-# LANGUAGE TypeApplications      #-}

module Tests.Arithmetization.Test3 (specArithmetization3) where

import           Prelude                         hiding (Num(..), Eq(..), Ord(..), Bool, (^), (/), (||), not, any, replicate)
import           Test.Hspec

import           ZkFold.Base.Algebra.Basic.Field (Zp)
import           ZkFold.Symbolic.Arithmetization (acValue, applyArgs, acValue)
import           ZkFold.Symbolic.Compiler        (compile)
import           ZkFold.Symbolic.Data.Bool       (Bool (..))
import           ZkFold.Symbolic.Data.Ord        (Ord (..))
import           ZkFold.Symbolic.Types           (R, SmallField, Symbolic)

-- A comparison test
testFunc :: forall a . Symbolic a => a -> a -> Bool a
testFunc x y = x <= y

specArithmetization3 :: Spec
specArithmetization3 = do
    describe "Arithmetization test 3" $ do
        it "should pass" $ do
            let Bool r = compile @(Zp SmallField) (testFunc @R) :: Bool R
            Bool (acValue (applyArgs r [3, 5])) `shouldBe` testFunc @(Zp SmallField) 3 5