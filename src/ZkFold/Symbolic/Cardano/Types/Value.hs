module ZkFold.Symbolic.Cardano.Types.Value where

import           Prelude                          hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.UInt

type PolicyId b a = ByteString 224 b a
type AssetName b a = ByteString 256 b a

newtype Value n b a = Value { getValue :: Vector n (PolicyId b a, (AssetName b a, UInt 64 b a)) }

deriving instance (Arithmetic a, KnownNat n) => SymbolicData a (Value n ArithmeticCircuit a)
