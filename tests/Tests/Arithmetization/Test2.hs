{-# LANGUAGE TypeApplications #-}

module Tests.Arithmetization.Test2 (specArithmetization2) where

import           GHC.Generics                                (Par1 (..))
import           Prelude                                     hiding (Bool, Eq (..), Num (..), not, replicate, (/), (^),
                                                              (||))
import           Test.Hspec

import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (Fr)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.GroebnerBasis               (makeTheorem, verify)
import           ZkFold.Symbolic.Types                       (Symbolic)

-- A true statement.
tautology :: forall a . Symbolic a => Par1 a -> Par1 a -> Bool a
tautology x y = (x /= y) || (x == y)

specArithmetization2 :: Spec
specArithmetization2 = do
    describe "Arithmetization test 2" $ do
        it "should pass" $ do
            let r = compile @Fr (tautology @(ArithmeticCircuit Fr))
            verify (makeTheorem r) `shouldBe` True
