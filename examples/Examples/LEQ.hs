{-# LANGUAGE TypeApplications    #-}

module Examples.LEQ (exampleLEQ) where

import           Prelude                                     hiding (Num(..), Eq(..), Ord(..), Bool, (^), (/), (!!), (||), not, any)

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Symbolic.Data.Bool                   (Bool(..))
import           ZkFold.Symbolic.Data.Ord                    (Ord(..))
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Types                       (Symbolic)

-- | (<=) operation
leq :: forall a . Symbolic a => a -> a -> Bool a
leq x y = x <= y
          
exampleLEQ :: IO ()
exampleLEQ = do
    let file = "compiled_scripts/leq.json"

    putStrLn "\nExample: (<=) operation\n"

    compileIO @(Zp BLS12_381_Scalar) file (leq @(ArithmeticCircuit (Zp BLS12_381_Scalar)))