{-# LANGUAGE TypeApplications #-}

module Tests.Arithmetization.Test3 (specArithmetization3) where

import           Numeric.Natural                   (Natural)
import           Prelude                           hiding (Bool, Eq (..), Num (..), Ord (..), any, not, replicate, (/),
                                                    (^), (||))
import           Test.Hspec

import           ZkFold.Base.Algebra.Basic.Class   (fromConstant)
import           ZkFold.Base.Algebra.Basic.Field   (Zp)
import           ZkFold.Symbolic.Class             (Symbolic)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool         (Bool (..))
import           ZkFold.Symbolic.Data.FieldElement (FieldElement)
import           ZkFold.Symbolic.Data.Ord          ((<=))
import           ZkFold.Symbolic.Interpreter       (Interpreter (Interpreter))

type R = ArithmeticCircuit (Zp 97)

-- A comparison test
testFunc :: Symbolic c => FieldElement c -> FieldElement c -> Bool c
testFunc x y = x <= y

specArithmetization3 :: Spec
specArithmetization3 = do
    describe "Arithmetization test 3" $ do
        it "should pass" $ do
            let Bool r = compile @(Zp 97) (testFunc @R) :: Bool R
            Bool (Interpreter $ acValue (applyArgs r [3, 5])) `shouldBe` testFunc (fromConstant (3 :: Natural)) (fromConstant (5 :: Natural))
