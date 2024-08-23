{-# LANGUAGE TypeApplications #-}

module Examples.Eq (exampleEq) where

import           Prelude                                     hiding (Bool, Eq (..), Num (..), Ord (..), any, not, (!!),
                                                              (/), (^), (||))

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Symbolic.Class                       (Symbolic)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool                   (Bool (..))
import           ZkFold.Symbolic.Data.Eq                     (Eq (..))
import           ZkFold.Symbolic.Data.FieldElement           (FieldElement)

-- | (==) operation
eq :: Symbolic c => FieldElement c -> FieldElement c -> Bool c
eq x y = x == y

exampleEq :: IO ()
exampleEq = do
    let file = "compiled_scripts/eq.json"

    putStrLn "\nExample: (==) operation\n"

    compileIO @(Zp BLS12_381_Scalar) file (eq @(ArithmeticCircuit (Zp BLS12_381_Scalar) (Vector 2)))
