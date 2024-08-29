module Examples.BatchTransfer (exampleBatchTransfer) where

import           ZkFold.Base.Data.Vector                         (Vector)
import ZkFold.Symbolic.Cardano.Contracts.BatchTransfer           ( Tx, TxOut, batchTransfer, Tokens )
import ZkFold.Symbolic.Cardano.Types                             ( Bool, ByteString, Value )
import ZkFold.Symbolic.Class                           (Symbolic (..))
import ZkFold.Base.Algebra.Basic.Number (KnownNat)
import ZkFold.Symbolic.Data.Class (SymbolicData(..))
import ZkFold.Symbolic.Cardano.Types.Value (SingleAsset)


exampleBatchTransfer ::
    ( Symbolic c
    , KnownNat (TypeSize (SingleAsset c))
    , KnownNat (TypeSize (Value Tokens c))
    , SymbolicData (TxOut c, TxOut c)
    )  => Tx c -> Vector 5 (TxOut c, TxOut c, ByteString 256 c) -> Bool c
exampleBatchTransfer = batchTransfer
