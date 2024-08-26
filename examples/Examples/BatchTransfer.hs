{-# LANGUAGE TypeOperators #-}

module Examples.BatchTransfer (exampleBatchTransfer) where

import           Data.Type.Equality                              (type (~))

import           ZkFold.Base.Data.Vector                         (Vector)
import           ZkFold.Symbolic.Cardano.Contracts.BatchTransfer (Tx, TxOut, batchTransfer)
import           ZkFold.Symbolic.Cardano.Types                   (Bool, ByteString)
import           ZkFold.Symbolic.Class                           (Symbolic (BaseField))
import ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import ZkFold.Base.Algebra.Basic.Field (Zp)

type F = Zp BLS12_381_Scalar

exampleBatchTransfer :: (Symbolic c, BaseField c ~ F) => Tx c -> Vector 5 (TxOut c, TxOut c, ByteString 256 c) -> Bool c
exampleBatchTransfer = batchTransfer
