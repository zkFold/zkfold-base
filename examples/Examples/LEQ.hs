{-# LANGUAGE TypeApplications #-}

module Examples.LEQ (exampleLEQ) where

import           Prelude                                     hiding (Bool, Eq (..), Num (..), Ord (..), any, not, (!!),
                                                              (/), (^), (||))

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Base.Data.Vector                     (Vector)
import           ZkFold.Symbolic.Class                       (Symbolic)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool                   (Bool)
import           ZkFold.Symbolic.Data.FieldElement           (FieldElement)
import           ZkFold.Symbolic.Data.Ord                    ((<=))

-- | (<=) operation
leq :: Symbolic c => FieldElement c -> FieldElement c -> Bool c
leq x y = x <= y

exampleLEQ :: IO ()
exampleLEQ = do
    let file = "compiled_scripts/leq.json"

    putStrLn "\nExample: (<=) operation\n"

    compileIO @(Zp BLS12_381_Scalar) file (leq @(ArithmeticCircuit (Zp BLS12_381_Scalar) (Vector 2)))
