{-# LANGUAGE TypeApplications #-}

module Tests.Arithmetization.Test3 (specArithmetization3) where

import           Data.Functor.Identity           (Identity)
import           Prelude                         hiding (Bool, Eq (..), Num (..), Ord (..), any, not, replicate, (/),
                                                  (^), (||))
import           Test.Hspec

import           ZkFold.Base.Algebra.Basic.Field (Zp)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool       (Bool (..))
import           ZkFold.Symbolic.Data.Compare    ((<=))
import           ZkFold.Symbolic.Types           (Symbolic)

type R = ArithmeticCircuit (Zp 97)

-- A comparison test
testFunc :: forall a . Symbolic a => Identity a -> Identity a -> Bool a
testFunc x y = x <= y

specArithmetization3 :: Spec
specArithmetization3 = do
    describe "Arithmetization test 3" $ do
        it "should pass" $ do
            let r = compile @(Zp 97) (testFunc @R)
            let actual = acValue (applyArgs r [3, 5])
            let Bool expected = testFunc 3 5
            actual `shouldBe` expected
