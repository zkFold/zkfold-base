module ZkFold.Symbolic.Cardano.Types.OutputRef where

import           Prelude                         hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.ByteString (ByteString)
import           ZkFold.Symbolic.Data.UInt

type TxRefId a = ByteString 256 a
type TxRedIndex a = UInt 32 a

newtype OutputRef a = OutputRef (TxRefId a, TxRedIndex a)

deriving instance Arithmetic a => SymbolicData a (OutputRef (ArithmeticCircuit a))

outputRefId :: OutputRef a -> TxRefId a
outputRefId (OutputRef (x, _)) = x

outputRefIndex :: OutputRef a -> TxRedIndex a
outputRefIndex (OutputRef (_, i)) = i
