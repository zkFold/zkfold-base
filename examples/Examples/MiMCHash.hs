{-# LANGUAGE TypeApplications #-}

module Examples.MiMCHash (exampleMiMC) where

import           Prelude                                     hiding (Eq (..), Num (..), any, not, (!!), (/), (^), (||))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC        (mimcHash)
import           ZkFold.Symbolic.Compiler


exampleMiMC :: IO ()
exampleMiMC = do
    let nRounds = 220
        file = "compiled_scripts/mimcHash.json"

    putStrLn "\nExample: MiMC hash function\n"

    compileIO @(Zp BLS12_381_Scalar) file (mimcHash @(ArithmeticCircuit (Zp BLS12_381_Scalar)) nRounds zero)
