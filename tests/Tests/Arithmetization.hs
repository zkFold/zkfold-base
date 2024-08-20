{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.Arithmetization (specArithmetization) where

import           GHC.Generics                                (Par1)
import           Prelude
import           Test.Hspec
import           Test.QuickCheck
import           Tests.Arithmetization.Test1                 (specArithmetization1)
import           Tests.Arithmetization.Test2                 (specArithmetization2)
import           Tests.Arithmetization.Test3                 (specArithmetization3)
import           Tests.Arithmetization.Test4                 (specArithmetization4)

import           ZkFold.Base.Algebra.Basic.Class             (FromConstant, MultiplicativeMonoid)
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.MonadCircuit                (Arithmetic)

propCircuitInvariance :: (MultiplicativeMonoid a, Eq a) => ArithmeticCircuitTest a Par1 -> Bool
propCircuitInvariance act@(ArithmeticCircuitTest ac wi) =
    let ArithmeticCircuitTest ac' wi' = mapVarArithmeticCircuit act
        v   = ac `eval` wi
        v'  = ac' `eval` wi'
    in v == v'

specArithmetization' :: forall a . (FromConstant a a, Arithmetic a, Arbitrary a, Show a, Show (ArithmeticCircuitTest a Par1)) => IO ()
specArithmetization' = hspec $ do
    describe "Arithmetization specification" $ do
        describe "Variable mapping" $ do
            it "does not change the circuit" $ property $ propCircuitInvariance @a
        specArithmetization1 @a
        specArithmetization2
        specArithmetization3
        specArithmetization4

specArithmetization :: IO ()
specArithmetization = do
    specArithmetization' @(Zp BLS12_381_Scalar)
