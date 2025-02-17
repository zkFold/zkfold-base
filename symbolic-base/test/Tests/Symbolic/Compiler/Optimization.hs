{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Tests.Symbolic.Compiler.Optimization (specOptimization) where

import           Data.Binary                                (Binary)
import           GHC.Generics                               (Par1 (..), U1 (..), type (:*:))
import           Prelude                                    (Show, return, ($))
import           Test.Hspec
import           Test.QuickCheck.Property                   ((.&.), (===))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number           (Natural)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler                   (compile)
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit
import           ZkFold.Symbolic.Data.Bool                  (Bool (..))
import           ZkFold.Symbolic.MonadCircuit


testFunc :: forall a . (Arithmetic a, Binary a) => ArithmeticCircuit a U1 Par1 Par1
testFunc = fromCircuitF idCircuit $ \(Par1 i0) -> do
    i1 <- newRanged (fromConstant (1 :: Natural)) (at i0)
    i2 <- newAssigned (($ i1) + one)
    i3 <- newAssigned (($ i2) + one)
    i4 <- newAssigned (($ i3) + one)
    i5 <- newAssigned (($ i4) + ($ i0))
    constraint (($ i4) - fromConstant (4 :: Natural))
    return (Par1 i5)

testBool :: forall a . (Arithmetic a, Binary a) => ArithmeticCircuit a (U1 :*: U1) (Par1 :*: U1) Par1
testBool = compile @a identBool
    where
        identBool :: Bool c -> Bool c
        identBool x = x

testConst :: forall a . (Arithmetic a, Binary a) => ArithmeticCircuit a U1 Par1 Par1
testConst = fromCircuitF idCircuit $ \(Par1 i0) -> do
    i1 <- newAssigned (($ i0) + one)
    i2 <- newAssigned (($ i1) + one)
    i3 <- newAssigned (($ i2) + one)
    i4 <- newAssigned (($ i3) + one)
    constraint (($ i4) - fromConstant (5 :: Natural))
    return (Par1 i0)

testLinVar :: forall a . (Arithmetic a, Binary a) => ArithmeticCircuit a U1 Par1 Par1
testLinVar = fromCircuitF idCircuit $ \(Par1 i0) -> do
    i1 <- newAssigned (($ i0) + one)
    i2 <- newAssigned (($ i1) * ($ i0))
    return (Par1 i2)

specOptimization :: forall a . (Arithmetic a, Binary a, Show a) => Spec
specOptimization =
    describe "Compiler optimization specification" $ do
        let ac = optimize @a testFunc
        it "eval equal" $ do
            eval ac U1 (Par1 one) === (eval $ testFunc @a) U1 (Par1 one)
        it "number of constraint decreases" $ do
            acSizeN ac === 1
        it "number of variables decreases" $ do
            acSizeM ac === 0
        it "bool should pass" $ do
            acSizeN (testBool @a :: ArithmeticCircuit a (U1 :*: U1) (Par1 :*: U1) Par1) === 1
        let constAc = optimize @a testConst
        it "constant ac evaluated" $ do
            eval constAc U1 (Par1 one) === (eval $ testConst @a) U1 (Par1 one)
        it "number of constraint and variables decreases" $ do
            acSizeM constAc === 0 .&. acSizeM constAc === 0
        let linVarAc = optimize @a testLinVar
        it "linVar ac evaluated" $ do
            eval linVarAc U1 (Par1 $ one + one) === (eval $ testLinVar @a) U1 (Par1 $ one + one)
        it "number of constraint and variables decreases" $ do
            acSizeM linVarAc === 1 .&. acSizeM linVarAc === 1
