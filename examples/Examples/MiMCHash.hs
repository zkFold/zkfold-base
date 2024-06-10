{-# LANGUAGE TypeApplications #-}

module Examples.MiMCHash (exampleMiMC) where

import           GHC.Generics                                (Par1 (..))
import           Prelude                                     hiding (Eq (..), Num (..), any, not, (!!), (/), (^), (||))

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Symbolic.Algorithms.Hash.MiMC        (hash)
import           ZkFold.Symbolic.Compiler

type F = Zp BLS12_381_Scalar
type A = ArithmeticCircuit F

mimc :: Par1 A -> Par1 A
mimc = Par1 . hash

exampleMiMC :: IO ()
exampleMiMC = do
    let file = "compiled_scripts/mimcHash.json"

    putStrLn "\nExample: MiMC hash function\n"

    compileIO @F file mimc
