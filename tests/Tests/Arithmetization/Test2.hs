{-# LANGUAGE TypeApplications #-}

module Tests.Arithmetization.Test2 (specArithmetization2) where

import Test.Hspec
import ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (Fr)
import ZkFold.Symbolic.Compiler
import ZkFold.Symbolic.Data.Bool (Bool (..), BoolType (..))
import ZkFold.Symbolic.Data.Eq (Eq (..))
import ZkFold.Symbolic.GroebnerBasis (makeTheorem, verify)
import ZkFold.Symbolic.Types (Symbolic)
import Prelude hiding (Bool, Eq (..), Num (..), not, replicate, (/), (^), (||))

-- A true statement.
tautology :: forall a. (Symbolic a) => a -> a -> Bool a
tautology x y = (x /= y) || (x == y)

specArithmetization2 :: Spec
specArithmetization2 = do
  describe "Arithmetization test 2" $ do
    it "should pass" $ do
      let Bool r = compile @Fr (tautology @(ArithmeticCircuit Fr)) :: Bool (ArithmeticCircuit Fr)
      verify (makeTheorem r) `shouldBe` True
