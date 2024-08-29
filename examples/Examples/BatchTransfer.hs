module Examples.BatchTransfer (exampleBatchTransfer) where

import           ZkFold.Base.Data.Vector                         (Vector)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC            (MiMCHash)
import           ZkFold.Symbolic.Cardano.Contracts.BatchTransfer (Tx, TxOut, batchTransfer)
import           ZkFold.Symbolic.Cardano.Types                   (Bool, ByteString)
import           ZkFold.Symbolic.Class                           (Symbolic (BaseField))
import           ZkFold.Symbolic.Data.Eq                         (Eq)


exampleBatchTransfer ::
    ( Symbolic c
    , MiMCHash (BaseField c) c (TxOut c, TxOut c)
    , Eq (Bool c) (TxOut c)
    )  => Tx c -> Vector 5 (TxOut c, TxOut c, ByteString 256 c) -> Bool c
exampleBatchTransfer = batchTransfer
