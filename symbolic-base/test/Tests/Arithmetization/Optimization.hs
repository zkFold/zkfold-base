{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.Arithmetization.Optimization (specOptimization) where

import           Data.Binary                                (Binary)
import           GHC.Generics                               (Par1 (..), U1 (..))
import           Prelude                                    (IO, Show, return, ($))
import           Test.Hspec
import           Test.QuickCheck.Property                   ((===))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Number           (Natural)
import           ZkFold.Symbolic.Class
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit
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

specOptimization :: forall a . (Arithmetic a, Binary a, Show a) => IO ()
specOptimization = hspec $ do
    describe "Optimization specification" $ do
        specOptimization' @a
