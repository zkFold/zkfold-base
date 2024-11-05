{-# LANGUAGE TypeOperators #-}

module Examples.UInt (
    exampleUIntMul,
    exampleUIntDivMod,
    exampleUIntStrictAdd,
    exampleUIntStrictMul,
    exampleUIntResize
  ) where

import           Control.DeepSeq                  (NFData)
import           Data.Type.Equality               (type (~))
import           GHC.TypeNats

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector          (Vector)
import           ZkFold.Symbolic.Class            (Symbolic (BaseField))
import           ZkFold.Symbolic.Data.Combinators (KnownRegisterSize, NumberOfRegisters, Ceil, GetRegisterSize)
import           ZkFold.Symbolic.Data.UInt        (StrictNum (..), UInt, OrdWord)

exampleUIntMul ::
  (KnownNat n, KnownRegisterSize r, Symbolic c) =>
  UInt n r c -> UInt n r c -> UInt n r c
exampleUIntMul = (*)

exampleUIntDivMod ::
  (KnownNat n, KnownRegisterSize r, Symbolic c,
   NumberOfRegisters (BaseField c) n r ~ k,
   KnownNat (Ceil (GetRegisterSize (BaseField c) n r) OrdWord),
   KnownNat k, NFData (c (Vector k))) =>
  UInt n r c -> UInt n r c -> (UInt n r c, UInt n r c)
exampleUIntDivMod = divMod

exampleUIntStrictAdd ::
  (KnownNat n, KnownRegisterSize r, Symbolic c) =>
  UInt n r c -> UInt n r c -> UInt n r c
exampleUIntStrictAdd = strictAdd

exampleUIntStrictMul ::
  (KnownNat n, KnownRegisterSize r, Symbolic c) =>
  UInt n r c -> UInt n r c -> UInt n r c
exampleUIntStrictMul = strictMul

exampleUIntResize ::
  (KnownNat n, KnownNat k, KnownRegisterSize r, Symbolic c) =>
  UInt n r c -> UInt k r c
exampleUIntResize = resize
