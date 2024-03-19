{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Examples.UInt (exampleUIntAdd, exampleUIntMul) where

import           Data.Data                                   (Proxy (Proxy))
import           Data.Function                               (($))
import           Data.List                                   ((++))
import           Data.String                                 (String)
import           GHC.TypeNats                                (KnownNat, natVal)
import           System.IO                                   (IO, putStrLn)
import           Text.Show                                   (show)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit, compileIO)
import           ZkFold.Symbolic.Data.UInt                   (UInt)

exampleUIntAdd :: forall n . KnownNat n => IO ()
exampleUIntAdd = makeExample @n "+" "add" (+)

exampleUIntMul :: forall n . KnownNat n => IO ()
exampleUIntMul = makeExample @n "*" "mul" (*)

makeExample ::
    forall n . KnownNat n => String -> String ->
    (forall a . (AdditiveMonoid (UInt n a), MultiplicativeMonoid (UInt n a)) => UInt n a -> UInt n a -> UInt n a) -> IO ()
makeExample shortName name op = do
    let n = show $ natVal (Proxy @n)
    putStrLn $ "\nExample: (" ++ shortName ++ ") operation on UInt" ++ n
    let file = "compiled_scripts/uint" ++ n ++ "_" ++ name ++ ".json"
    compileIO @(Zp BLS12_381_Scalar) file (op @(ArithmeticCircuit (Zp BLS12_381_Scalar)))
