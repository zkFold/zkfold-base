{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeOperators       #-}

module Examples.FFA (examplesFFA) where

import           Data.Function                               (($))
import           Data.List                                   ((++))
import           Data.String                                 (String)
import           System.IO                                   (IO, putStrLn)
import           Text.Show                                   (show)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.Basic.Number
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Symbolic.Compiler                    (ArithmeticCircuit, compileIO)
import           ZkFold.Symbolic.Data.FFA                    (FFA)

type Prime256_1 = 28948022309329048855892746252171976963363056481941560715954676764349967630337
type Prime256_2 = 28948022309329048855892746252171976963363056481941647379679742748393362948097

examplesFFA :: IO ()
examplesFFA = do
  exampleFFAadd @Prime256_1
  exampleFFAadd @Prime256_2
  exampleFFAmul @Prime256_1
  exampleFFAmul @Prime256_2

exampleFFAadd :: forall p. KnownNat p => IO ()
exampleFFAadd = makeExample @p "+" "add" (+)

exampleFFAmul :: forall p. KnownNat p => IO ()
exampleFFAmul = makeExample @p "*" "mul" (*)

type Binary a = a -> a -> a

makeExample :: forall p. KnownNat p => String -> String -> Binary (FFA p (ArithmeticCircuit (Zp BLS12_381_Scalar) (Vector 14))) -> IO ()
makeExample shortName name op = do
    let p = show $ value @p
    putStrLn $ "\nExample: (" ++ shortName ++ ") operation on FFA " ++ p
    let file = "compiled_scripts/ffa_" ++ p ++ "_" ++ name ++ ".json"
    compileIO @14 @(Zp BLS12_381_Scalar) file op
