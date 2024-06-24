module ZkFold.Symbolic.Cardano.Types.Value where

import           Prelude                          hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.UInt

type PolicyId a = ByteString 224 a
type AssetName a = ByteString 256 a

newtype Value n a = Value { getValue :: Vector n (PolicyId a, (AssetName a, UInt 64 a)) }

deriving instance (Arithmetic a, KnownNat n) => SymbolicData a (Value n (ArithmeticCircuit a))
