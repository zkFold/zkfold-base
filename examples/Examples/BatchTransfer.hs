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
    , SymbolicData (TxOut c)
    , KnownNat (TypeSize (TxOut c))
    , KnownNat (TypeSize (SingleAsset c))
    , KnownNat (TypeSize (Value Tokens c))
    )  => Tx c -> Vector 5 (TxOut c, TxOut c, ByteString 256 c) -> Bool c
exampleBatchTransfer = batchTransfer
