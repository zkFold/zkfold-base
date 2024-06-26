{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module ZkFold.Symbolic.Cardano.Types.Input where

import           Prelude                                 hiding (Bool, Eq, length, splitAt, (*), (+))

import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Symbolic.Cardano.Types.Address   (Address)
import           ZkFold.Symbolic.Cardano.Types.Output    (DatumHash, Output, txoAddress, txoDatumHash, txoTokens)
import           ZkFold.Symbolic.Cardano.Types.OutputRef (OutputRef)
import           ZkFold.Symbolic.Cardano.Types.Value     (Value)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.ByteString         (ByteString)
import           ZkFold.Symbolic.Data.Combinators        (NumberOfRegisters)
import           ZkFold.Symbolic.Data.UInt               (UInt)

newtype Input tokens datum b a = Input (OutputRef b a, Output tokens datum b a)

deriving instance
    ( Arithmetic a
    , KnownNat (TypeSize a (Value tokens ArithmeticCircuit a))
    , KnownNat (256 + NumberOfRegisters a 32)
    , KnownNat (TypeSize a (ByteString 224 ArithmeticCircuit a, (ByteString 256 ArithmeticCircuit a, UInt 64 ArithmeticCircuit a)))
    ) => SymbolicData a (Input tokens datum ArithmeticCircuit a)

txiOutputRef :: Input tokens datum b a -> OutputRef b a
txiOutputRef (Input (ref, _)) = ref

txiOutput :: Input tokens datum b a -> Output tokens datum b a
txiOutput (Input (_, txo)) = txo

txiAddress :: Input tokens datum b a -> Address b a
txiAddress (Input (_, txo)) = txoAddress txo

txiTokens :: Input tokens datum b a -> Value tokens b a
txiTokens (Input (_, txo)) = txoTokens txo

txiDatumHash :: Input tokens datum b a -> DatumHash b a
txiDatumHash (Input (_, txo)) = txoDatumHash txo
