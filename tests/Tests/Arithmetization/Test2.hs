{-# LANGUAGE TypeApplications      #-}

module Tests.Arithmetization.Test2 (specArithmetization2) where

import           Prelude                                     hiding (Num(..), Eq(..), Bool, (^), (/), (||), not, replicate)
import           Test.Hspec

import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (Fr)
import           ZkFold.Symbolic.Compiler                    (compile)
import           ZkFold.Symbolic.Data.Bool                   (BoolType(..), Bool (..))
import           ZkFold.Symbolic.Data.Eq                     (Eq (..))
import           ZkFold.Symbolic.GroebnerBasis               (verify, makeTheorem)
import           ZkFold.Symbolic.Types                       (Symbolic)

import ZkFold.Symbolic.Arithmetization (ArithmeticCircuit)

-- A true statement.
tautology :: forall a . Symbolic a => a -> a -> Bool a
tautology x y = (x /= y) || (x == y)

specArithmetization2 :: Spec
specArithmetization2 = do
    describe "Arithmetization test 2" $ do
        it "should pass" $ do
            let Bool r = compile @Fr (tautology @(ArithmeticCircuit Fr)) :: Bool (ArithmeticCircuit Fr)
            verify (makeTheorem r) `shouldBe` True