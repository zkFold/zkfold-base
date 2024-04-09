{-# LANGUAGE TypeApplications #-}

module Examples.Eq (exampleEq) where

import ZkFold.Base.Algebra.Basic.Field (Zp)
import ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import ZkFold.Symbolic.Compiler
import ZkFold.Symbolic.Data.Bool (Bool (..))
import ZkFold.Symbolic.Data.Eq (Eq (..))
import ZkFold.Symbolic.Types (Symbolic)
import Prelude hiding (Bool, Eq (..), Num (..), Ord (..), any, not, (!!), (/), (^), (||))

-- | (==) operation
eq :: forall a. (Symbolic a) => a -> a -> Bool a
eq x y = x == y

exampleEq :: IO ()
exampleEq = do
  let file = "compiled_scripts/eq.json"

  putStrLn "\nExample: (==) operation\n"

  compileIO @(Zp BLS12_381_Scalar) file (eq @(ArithmeticCircuit (Zp BLS12_381_Scalar)))
