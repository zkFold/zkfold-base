{-# LANGUAGE TypeApplications #-}

module Examples.BatchTransfer (exampleBatchTransfer) where

import           Prelude                                         hiding (Eq (..), Num (..), any, not, (!!), (/), (^),
                                                                  (||))

import           ZkFold.Base.Algebra.Basic.Field                 (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381     (BLS12_381_Scalar)
import           ZkFold.Symbolic.Cardano.Contracts.BatchTransfer (batchTransfer)
import           ZkFold.Symbolic.Compiler                        (ArithmeticCircuit, compileIO)

exampleBatchTransfer :: IO ()
exampleBatchTransfer = do
    let file = "compiled_scripts/batch-transfer.json"

    putStrLn "\nExample: Batch Transfer smart contract\n"

    compileIO @(Zp BLS12_381_Scalar) file (batchTransfer @ArithmeticCircuit  @(Zp BLS12_381_Scalar))
