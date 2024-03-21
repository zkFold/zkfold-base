{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.Arithmetization (specArithmetization) where

import           Data.Map                        (fromList)
import           Prelude
import           Test.Hspec
import           Test.QuickCheck

import           Tests.Arithmetization.Test1     (specArithmetization1)
import           Tests.Arithmetization.Test2     (specArithmetization2)
import           Tests.Arithmetization.Test3     (specArithmetization3)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Compiler.ArithmeticCircuit.Internal
import           ZkFold.Symbolic.Types           (Symbolic)

-- propCircuitInvariance :: Arithmetic a => (ArithmeticCircuit a, a, a) -> Bool
-- propCircuitInvariance (ac, x, y) =
    -- let ac' = mapVarArithmeticCircuit ac
        -- v   = ac `eval` fromList [(1, x), (2, y)]
        -- v'  = ac' `eval` fromList [(1, x), (2, y)]
    -- in v == v'

specArithmetization :: forall a . (Symbolic a, Arithmetic a, Arbitrary a, Show a) => IO ()
specArithmetization = hspec $ do
    describe "Arithmetization specification" $ do
        -- describe "Variable mapping" $ do
            -- it "does not change the circuit" $ property $ propCircuitInvariance @a
        -- specArithmetization1 @a
        specArithmetization2
        -- specArithmetization3
