{-# LANGUAGE TypeOperators #-}

module Examples.BatchTransfer (exampleBatchTransfer) where

import           Data.Type.Equality                              (type (~))

import           ZkFold.Base.Data.Vector                         (Vector)
import           ZkFold.Symbolic.Cardano.Contracts.BatchTransfer (Tx, TxOut, batchTransfer)
import           ZkFold.Symbolic.Cardano.Types                   (Bool, ByteString, F)
import           ZkFold.Symbolic.Class                           (Symbolic (BaseField))
import           ZkFold.Symbolic.Data.Eq                         (Eq)

exampleBatchTransfer ::
  (Symbolic c, BaseField c ~ F, Eq (Bool c) (TxOut c)) =>
  Tx c -> Vector 5 (TxOut c, TxOut c, ByteString 256 c) -> Bool c
exampleBatchTransfer = batchTransfer
