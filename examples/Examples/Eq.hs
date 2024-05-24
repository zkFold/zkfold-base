{-# LANGUAGE TypeApplications #-}

module Examples.Eq (exampleEq) where

import           Data.Functor.Identity                       (Identity)
import           Prelude                                     hiding (Bool, Eq (..), Num (..), Ord (..), any, not, (!!),
                                                              (/), (^), (||))

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Bool                   (Eq (..))

exampleEq :: IO ()
exampleEq = do
    let file = "compiled_scripts/eq.json"

    putStrLn "\nExample: (==) operation\n"

    compileIO @(Zp BLS12_381_Scalar) file ((==) @(ArithmeticCircuit (Zp BLS12_381_Scalar)) @Identity)
