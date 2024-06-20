module ZkFold.Symbolic.Cardano.Types.OutputRef where

import           Prelude                         hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.ByteString (ByteString)
import           ZkFold.Symbolic.Data.UInt

type TxRefId b a = ByteString 256 b a
type TxRedIndex b a = UInt 32 b a

newtype OutputRef b a = OutputRef (TxRefId b a, TxRedIndex b a)

deriving instance Arithmetic a => SymbolicData a (OutputRef ArithmeticCircuit a)

outputRefId :: OutputRef b a -> TxRefId b a
outputRefId (OutputRef (x, _)) = x

outputRefIndex :: OutputRef b a -> TxRedIndex b a
outputRefIndex (OutputRef (_, i)) = i
