{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module Examples.BatchTransfer (exampleBatchTransfer) where

import           Prelude                                         hiding (Eq (..), Num (..), any, not, (!!), (/), (^),
                                                                  (||))

import           ZkFold.Symbolic.Cardano.Contracts.BatchTransfer (batchTransfer)
import           ZkFold.Symbolic.Compiler                        (compileIO)

exampleBatchTransfer :: IO ()
exampleBatchTransfer = do
    let file = "compiled_scripts/batch-transfer.json"

    putStrLn "\nExample: Batch Transfer smart contract\n"

    compileIO file batchTransfer
