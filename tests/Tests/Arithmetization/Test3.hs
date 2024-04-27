{-# LANGUAGE TypeApplications #-}

module Tests.Arithmetization.Test3 (specArithmetization3) where

import           Prelude                          hiding (Bool, Eq (..), Num (..), Ord (..), any, not, replicate, (/),
                                                   (^), (||))
import           Test.Hspec

import           ZkFold.Base.Algebra.Basic.Field  (Zp)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool        (Bool (..))
import           ZkFold.Symbolic.Data.Ord         (Ord (..))
import           ZkFold.Symbolic.Types            (Symbolic)

type R = ArithmeticCircuit (Zp 97)

-- A comparison test
testFunc :: forall a . Symbolic a => a -> a -> Bool a
testFunc x y = x <= y

specArithmetization3 :: Spec
specArithmetization3 = do
    describe "Arithmetization test 3" $ do
        it "should pass" $ do
            let Bool r = compile @(Zp 97) (testFunc @R) :: Bool R
            Bool (acValue (applyArgs r [3, 5])) `shouldBe` testFunc 3 5

