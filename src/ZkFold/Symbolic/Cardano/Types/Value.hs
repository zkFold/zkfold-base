{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module ZkFold.Symbolic.Cardano.Types.Value where

import           Prelude                           hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Data.Vector
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.ByteString
import qualified ZkFold.Symbolic.Data.FieldElement as FE
import           ZkFold.Symbolic.Data.UInt

type PolicyId b a    = ByteString 224 b a
type AssetName b a   = ByteString 256 b a
type SingleAsset b a = (PolicyId b a, (AssetName b a, UInt 64 b a))

newtype Value n b a = Value { getValue :: Vector n (SingleAsset b a) }

deriving instance
    ( Arithmetic a
    , KnownNat (FE.TypeSize a Vector (ByteString 224 Vector a, (ByteString 256 Vector a, UInt 64 Vector a)))
    ) => FE.FieldElementData a Vector (Value n Vector a)

deriving instance
    ( Arithmetic a
    , KnownNat (TypeSize a (ByteString 224 ArithmeticCircuit a, (ByteString 256 ArithmeticCircuit a, UInt 64 ArithmeticCircuit a)))
    ) => SymbolicData a (Value n ArithmeticCircuit a)
