module ZkFold.Symbolic.Cardano.Types.OutputRef where

import           Prelude                         hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.ByteString (ByteString)
import           ZkFold.Symbolic.Data.UInt

newtype OutputRef a = OutputRef (ByteString 256 a, UInt 32 a)

deriving instance Arithmetic a => SymbolicData a (OutputRef (ArithmeticCircuit a))