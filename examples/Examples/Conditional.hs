{-# LANGUAGE TypeApplications    #-}

module Examples.Conditional (exampleConditional) where

import           Prelude                                     (IO, Integer, putStrLn)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Symbolic.Data.Bool                   (Bool)
import           ZkFold.Symbolic.Data.Conditional            (Conditional(..))
import           ZkFold.Symbolic.Data.Eq                     (Eq(..))
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Types                       (Symbolic)

-- | if x == y then 5 else 3
ifEq :: forall a . Symbolic a => a -> a -> a
ifEq x y = bool @(Bool a) (fromConstant (3 :: Integer)) (fromConstant (5 :: Integer)) (x == y)
          
exampleConditional :: IO ()
exampleConditional = do
    let file = "compiled_scripts/if.json"

    putStrLn "\nExample: ifEq\n"

    compileIO @(Zp BLS12_381_Scalar) file (ifEq @(ArithmeticCircuit (Zp BLS12_381_Scalar)))