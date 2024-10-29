module Examples.BatchTransfer (exampleBatchTransfer) where

import           GHC.TypeLits                                    (KnownNat)

import           ZkFold.Base.Data.Vector                         (Vector)
import           ZkFold.Symbolic.Cardano.Contracts.BatchTransfer (Tx, TxOut, batchTransfer)
import           ZkFold.Symbolic.Cardano.Types                   (Bool, ByteString)
import           ZkFold.Symbolic.Class                           (Symbolic (..))
import           ZkFold.Symbolic.Data.Combinators                (NumberOfRegisters, RegisterSize (..))
import ZkFold.Symbolic.Data.Input (SymbolicInput)

exampleBatchTransfer ::
    ( Symbolic c
    , SymbolicInput (TxOut c)
    , KnownNat (NumberOfRegisters (BaseField c) 64 'Auto)
    , KnownNat (NumberOfRegisters (BaseField c) 256 'Auto)
    )  => Tx c -> Vector 5 (TxOut c, TxOut c, ByteString 256 c) -> Bool c
exampleBatchTransfer = batchTransfer
