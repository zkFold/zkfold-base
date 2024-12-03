{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Tests.Arithmetization.Optimization (specOptimization) where

import           Data.Binary                                (Binary)
import           GHC.Generics                               (Par1 (..), U1 (..), type (:*:) )
import           Prelude                                    (IO, Show, return, ($))
import           Test.Hspec
import           Test.QuickCheck.Property                   ((===), (.&.))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number           (Natural)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit
import           ZkFold.Symbolic.MonadCircuit
import ZkFold.Symbolic.Data.Bool ( Bool(..) )
import ZkFold.Symbolic.Compiler (compile)


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
testBool = ac
    where
        identBool :: Bool c -> Bool c
        identBool x = x

        Bool ac = compile @a identBool

testConst :: forall a . (Arithmetic a, Binary a) => ArithmeticCircuit a U1 Par1 Par1
testConst = fromCircuitF idCircuit $ \(Par1 i0) -> do
    i1 <- newAssigned (($ i0) + one)
    i2 <- newAssigned (($ i1) + one)
    i3 <- newAssigned (($ i2) + one)
    i4 <- newAssigned (($ i3) + one)
    constraint (($ i4) - fromConstant (5 :: Natural))
    return (Par1 i0)

specOptimization' :: forall a . (Arithmetic a, Binary a, Show a) => Spec
specOptimization' = do
    describe "Arithmetization optimization test" $ do
        let ac = optimize @a testFunc
        it "eval equal" $ do
            eval ac U1 (Par1 one) === (eval $ testFunc @a) U1 (Par1 one)
        it "number of constraint decreases" $ do
            acSizeN ac === 1
        it "number of variables decreases" $ do
            acSizeM ac === 1
        it "bool should pass" $ do
            acSizeN (testBool @a :: ArithmeticCircuit a (U1 :*: U1) (Par1 :*: U1) Par1) === 1
        let constAc = optimize @a testConst
        it "constant ac evaluated" $ do
            eval constAc U1 (Par1 one) === (eval $ testConst @a) U1 (Par1 one)
        it "number of constraint and variables decreases" $ do
            acSizeM constAc === 0 .&. acSizeM constAc === 0


specOptimization :: forall a . (Arithmetic a, Binary a, Show a) => IO ()
specOptimization = hspec $ do
    describe "Optimization specification" $ do
        specOptimization' @a
