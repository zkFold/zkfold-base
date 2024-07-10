{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module Main where

import           Examples.BatchTransfer (exampleBatchTransfer)
import           Examples.ByteString    (exampleByteStringAnd, exampleByteStringExtend, exampleByteStringOr)
import           Examples.Conditional   (exampleConditional)
import           Examples.Eq            (exampleEq)
import           Examples.FFA           (examplesFFA)
import           Examples.Fibonacci     (exampleFibonacci)
import           Examples.LEQ           (exampleLEQ)
import           Examples.MiMCHash      (exampleMiMC)
import           Examples.ReverseList   (exampleReverseList)
import           Examples.UInt          (exampleUIntAdd, exampleUIntMul, exampleUIntStrictAdd, exampleUIntStrictMul)
import           Prelude
import           System.Directory       (createDirectoryIfMissing)

main :: IO ()
main = do
    createDirectoryIfMissing True "compiled_scripts"

    exampleReverseList
    exampleEq
    exampleFibonacci
    exampleMiMC
    exampleLEQ
    exampleConditional
    exampleUIntAdd @32
    exampleUIntAdd @500
    exampleUIntMul @32
    exampleUIntMul @500
    examplesFFA
    exampleUIntStrictAdd @32
    exampleUIntStrictAdd @500
    exampleUIntStrictMul @32
    exampleUIntStrictMul @500
    exampleByteStringAnd @32
    exampleByteStringAnd @500
    exampleByteStringOr @32
    exampleByteStringOr @500
    exampleByteStringExtend @1 @512

    exampleBatchTransfer
