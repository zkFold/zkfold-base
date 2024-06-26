{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module ZkFold.Symbolic.Cardano.Types.Output where

import           Prelude                               hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Symbolic.Cardano.Types.Address (Address)
import           ZkFold.Symbolic.Cardano.Types.Value   (Value)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool             (Bool)
import           ZkFold.Symbolic.Data.ByteString
import           ZkFold.Symbolic.Data.Eq               (Eq)
import           ZkFold.Symbolic.Data.Eq.Structural
import           ZkFold.Symbolic.Data.UInt             (UInt)

type DatumHash b a = ByteString 256 b a

newtype Output tokens datum b a = Output (Address b a, (Value tokens b a, DatumHash b a))

deriving instance
    ( Arithmetic a
    , KnownNat (TypeSize a (Value tokens ArithmeticCircuit a))
    , KnownNat (TypeSize a (ByteString 224 ArithmeticCircuit a, (ByteString 256 ArithmeticCircuit a, UInt 64 ArithmeticCircuit a)))
    ) => SymbolicData a (Output tokens datum ArithmeticCircuit a)

deriving via (Structural (Output tokens datum ArithmeticCircuit a))
         instance
            ( Arithmetic a
            , ts ~ TypeSize a (Output tokens datum ArithmeticCircuit a)
            , 1 <= ts
            , KnownNat ts
            , KnownNat (TypeSize a (Value tokens ArithmeticCircuit a))
            , KnownNat (TypeSize a (ByteString 224 ArithmeticCircuit a, (ByteString 256 ArithmeticCircuit a, UInt 64 ArithmeticCircuit a)))
            ) => Eq (Bool (ArithmeticCircuit 1 a)) (Output tokens datum ArithmeticCircuit a)


txoAddress :: Output tokens datum b a -> Address b a
txoAddress (Output (addr, _)) = addr

txoTokens :: Output tokens datum b a -> Value tokens b a
txoTokens (Output (_, (v, _))) = v

txoDatumHash :: Output tokens datum b a -> DatumHash b a
txoDatumHash (Output (_, (_, dh))) = dh
