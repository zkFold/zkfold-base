{-# LANGUAGE TypeApplications #-}

module Examples.Conditional (exampleConditional) where

import           GHC.Generics                                (Par1)
import           Prelude                                     (IO, putStrLn)

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool                   (bool)

type F = Zp BLS12_381_Scalar
type A = ArithmeticCircuit F

exampleConditional :: IO ()
exampleConditional = do
    let file = "compiled_scripts/conditional.json"

    putStrLn "\nExample: conditional\n"

    compileIO @F file (bool @A @Par1)
