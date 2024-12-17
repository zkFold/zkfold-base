module Examples.UInt (
    exampleUIntMul,
    exampleUIntDivMod,
    exampleUIntStrictAdd,
    exampleUIntStrictMul,
    exampleUIntResize
  ) where

import           Control.DeepSeq                  (NFData)
import           GHC.TypeNats

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Symbolic.Class            (Symbolic (BaseField))
import           ZkFold.Symbolic.Data.Combinators (KnownRegisterSize, resize)
import           ZkFold.Symbolic.Data.UInt        (RegistersOf, StrictNum (..), UInt)

exampleUIntMul ::
  (KnownNat n, KnownRegisterSize r, Symbolic c) =>
  UInt n r c -> UInt n r c -> UInt n r c
exampleUIntMul = (*)

exampleUIntDivMod ::
  (KnownNat n, KnownRegisterSize r, Symbolic c,
   NFData (c (RegistersOf n r (BaseField c)))) =>
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
