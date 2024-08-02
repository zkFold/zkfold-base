{-# LANGUAGE TypeApplications #-}

module Examples.MiMCHash (exampleMiMC) where

import           GHC.Generics                                   (Par1)
import           Prelude                                        hiding (Eq (..), Num (..), any, not, (!!), (/), (^),
                                                                 (||))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field                (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381    (BLS12_381_Scalar)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC           (mimcHash2)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC.Constants (mimcConstants)
import           ZkFold.Symbolic.Compiler

type F = Zp BLS12_381_Scalar

exampleMiMC :: IO ()
exampleMiMC = do
    let file = "compiled_scripts/mimcHash.json"

    putStrLn "\nExample: MiMC hash function\n"

    compileIO @F file (mimcHash2 @F @(ArithmeticCircuit F Par1) mimcConstants zero)
