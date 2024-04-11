{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators    #-}

module Examples.ByteString (
    exampleByteStringAnd,
    exampleByteStringOr, 
    exampleByteStringGrow
  ) where

import           Data.Data                                   (Proxy (Proxy))
import           Data.Function                               (($))
import           Data.List                                   ((++))
import           Data.String                                 (String)
import           GHC.TypeNats                                (KnownNat, natVal, type (<=))
import           System.IO                                   (IO, putStrLn)
import           Text.Show                                   (show)

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit, compileIO)
import           ZkFold.Symbolic.Data.Bool
import           ZkFold.Symbolic.Data.ByteString

exampleByteStringAnd :: forall n . KnownNat n => IO ()
exampleByteStringAnd = makeExample @n "*" "and" (&&)

exampleByteStringOr :: forall n . KnownNat n => IO ()
exampleByteStringOr = makeExample @n "+" "or" (||)

exampleByteStringGrow :: forall n k . (KnownNat n, KnownNat k, n <= k) => IO ()
exampleByteStringGrow = do
    let n = show $ natVal (Proxy @n)
    let k = show $ natVal (Proxy @k)
    putStrLn $ "\nExample: Extending a bytestring of length " ++ n ++ " to length " ++ k
    let file = "compiled_scripts/bytestring" ++ n ++ "_to_" ++ k ++ ".json"
    compileIO @(Zp BLS12_381_Scalar) file $ grow @(ByteString n (ArithmeticCircuit (Zp BLS12_381_Scalar))) @(ByteString k (ArithmeticCircuit (Zp BLS12_381_Scalar)))

type Binary a = a -> a -> a

type UBinary n = Binary (ByteString n (ArithmeticCircuit (Zp BLS12_381_Scalar)))

makeExample :: forall n . KnownNat n => String -> String -> UBinary n -> IO ()
makeExample shortName name op = do
    let n = show $ natVal (Proxy @n)
    putStrLn $ "\nExample: (" ++ shortName ++ ") operation on ByteString" ++ n
    let file = "compiled_scripts/bytestring" ++ n ++ "_" ++ name ++ ".json"
    compileIO @(Zp BLS12_381_Scalar) file op
