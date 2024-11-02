{-# LANGUAGE TypeOperators #-}

module Examples.UInt (
    exampleUIntMul,
    exampleUIntDivMod,
    exampleUIntStrictAdd,
    exampleUIntStrictMul,
    exampleUIntResize,
    exampleUIntXor,
    exampleUIntRotate5,
    exampleUIntIso
  ) where

import           GHC.TypeNats
import           Control.DeepSeq                  (NFData)
import           Data.Type.Equality               (type (~))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Data.Vector          (Vector)
import           ZkFold.Symbolic.Class            (Symbolic (BaseField))
import           ZkFold.Symbolic.Data.Combinators (KnownRegisterSize, NumberOfRegisters, Iso (..), Resize (..))
import           ZkFold.Symbolic.Data.UInt        (StrictNum (..), UInt)
import ZkFold.Symbolic.Data.Bool (BoolType(..))
import ZkFold.Symbolic.Data.ByteString (ByteString, ShiftBits (rotateBits))

exampleUIntMul ::
  (KnownNat n, KnownRegisterSize r, Symbolic c) =>
  UInt n r c -> UInt n r c -> UInt n r c
exampleUIntMul = (*)

exampleUIntDivMod ::
  (KnownNat n, KnownRegisterSize r, Symbolic c,
   NumberOfRegisters (BaseField c) n r ~ k,
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

exampleUIntXor ::
  (KnownNat n, KnownRegisterSize r, Symbolic c) =>
  UInt n r c -> UInt n r c -> UInt n r c
exampleUIntXor = xor

exampleUIntResize :: 
  (KnownNat n, KnownNat k, KnownRegisterSize r, Symbolic c) =>
  UInt n r c -> UInt k r c
exampleUIntResize = resize

exampleUIntRotate5 :: forall n r c.
  (KnownNat n, KnownRegisterSize r, Symbolic c) =>
  UInt n r c -> UInt n r c
exampleUIntRotate5 s = from (rotateBits (from s :: ByteString n c) 5) 

exampleUIntIso ::
  (KnownNat n, KnownRegisterSize r, Symbolic c) =>
  UInt n r c -> ByteString n c 
exampleUIntIso = from
