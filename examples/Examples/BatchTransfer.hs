module Examples.BatchTransfer (exampleBatchTransfer) where

import           ZkFold.Base.Algebra.Basic.Number                (KnownNat)
import           ZkFold.Base.Data.Vector                         (Vector)
import           ZkFold.Symbolic.Cardano.Contracts.BatchTransfer (Tokens, Tx, TxOut, batchTransfer)
import           ZkFold.Symbolic.Cardano.Types                   (Bool, ByteString, Value)
import           ZkFold.Symbolic.Cardano.Types.Value             (SingleAsset)
import           ZkFold.Symbolic.Class                           (Symbolic (..))
import           ZkFold.Symbolic.Data.Class                      (SymbolicData (..))


exampleBatchTransfer ::
    ( Symbolic c
    , KnownNat (TypeSize (SingleAsset c))
    , KnownNat (TypeSize (Value Tokens c))
    , SymbolicData (TxOut c, TxOut c)
    )  => Tx c -> Vector 5 (TxOut c, TxOut c, ByteString 256 c) -> Bool c
exampleBatchTransfer = batchTransfer
