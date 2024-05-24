{-# LANGUAGE TypeApplications #-}

module Examples.MiMCHash (exampleMiMC) where

import           Data.Functor.Identity                          (Identity)
import           Prelude                                        hiding (Eq (..), Num (..), any, not, (!!), (/), (^),
                                                                 (||))

import           ZkFold.Base.Algebra.Basic.Field                (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381    (BLS12_381_Scalar)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC           (hash)
import           ZkFold.Symbolic.Compiler

exampleMiMC :: IO ()
exampleMiMC = do
    let file = "compiled_scripts/mimcHash.json"

    putStrLn "\nExample: MiMC hash function\n"

    compileIO @(Zp BLS12_381_Scalar) file (hash @(ArithmeticCircuit (Zp BLS12_381_Scalar)) @Identity)
