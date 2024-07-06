{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}
{-# OPTIONS_GHC -freduction-depth=0 #-} -- Avoid reduction overflow error caused by NumberOfRegisters

module Examples.UInt (
    exampleUIntAdd,
    exampleUIntMul,
    exampleUIntStrictAdd,
    exampleUIntStrictMul
  ) where

import           Data.Data                                   (Proxy (Proxy))
import           Data.Function                               (($))
import           Data.List                                   ((++))
import           Data.String                                 (String)
import           GHC.TypeNats                                (KnownNat, natVal, type (+))
import           Prelude                                     (type (~))
import           System.IO                                   (IO, putStrLn)
import           Text.Show                                   (show)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit, compileIO)
import           ZkFold.Symbolic.Data.Combinators
import           ZkFold.Symbolic.Data.UInt

exampleUIntAdd
    :: forall n r
    .  KnownNat n
    => r ~ NumberOfRegisters (Zp BLS12_381_Scalar) n
    => KnownNat r
    => KnownNat (r + r)
    => IO ()
exampleUIntAdd = makeExample @n "+" "add" (+)

exampleUIntMul
    :: forall n r
    .  KnownNat n
    => r ~ NumberOfRegisters (Zp BLS12_381_Scalar) n
    => KnownNat r
    => KnownNat (r + r)
    => IO ()
exampleUIntMul = makeExample @n "*" "mul" (*)

exampleUIntStrictAdd
    :: forall n r
    .  KnownNat n
    => r ~ NumberOfRegisters (Zp BLS12_381_Scalar) n
    => KnownNat r
    => KnownNat (r + r)
    => IO ()
exampleUIntStrictAdd = makeExample @n "strictAdd" "strict_add" strictAdd

exampleUIntStrictMul
    :: forall n r
    .  KnownNat n
    => r ~ NumberOfRegisters (Zp BLS12_381_Scalar) n
    => KnownNat r
    => KnownNat (r + r)
    => IO ()
exampleUIntStrictMul = makeExample @n "strictMul" "strict_mul" strictMul

type Binary a = a -> a -> a

type UBinary n = Binary (UInt n ArithmeticCircuit (Zp BLS12_381_Scalar))

makeExample
    :: forall n r
    .  KnownNat n
    => r ~ NumberOfRegisters (Zp BLS12_381_Scalar) n
    => KnownNat r
    => KnownNat (r + r)
    => String -> String -> UBinary n -> IO ()
makeExample shortName name op = do
    let n = show $ natVal (Proxy @n)
    putStrLn $ "\nExample: (" ++ shortName ++ ") operation on UInt" ++ n
    let file = "compiled_scripts/uint" ++ n ++ "_" ++ name ++ ".json"
    compileIO @(Zp BLS12_381_Scalar) file op
