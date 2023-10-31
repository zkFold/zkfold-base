{-# LANGUAGE TypeApplications    #-}

module Examples.LEQ (exampleLEQ) where

import           Prelude                          hiding (Num(..), Eq(..), Ord(..), Bool, (^), (/), (!!), (||), not, any)

import           ZkFold.Base.Algebra.Basic.Field  (Zp)
import           ZkFold.Symbolic.Arithmetization  (acSizeM, acSizeN, ArithmeticCircuit)
import           ZkFold.Symbolic.Data.Bool        (Bool(..))
import           ZkFold.Symbolic.Data.Ord         (Ord(..))
import           ZkFold.Symbolic.Compiler         (compile)
import           ZkFold.Symbolic.Types            (Symbolic, BLS12_381_Scalar)

-- | (<=) operation
leq :: forall a . Symbolic a => a -> a -> Bool a
leq x y = x <= y
          
exampleLEQ :: IO ()
exampleLEQ = do
    let ac   = compile @(Zp BLS12_381_Scalar) (leq @(ArithmeticCircuit (Zp BLS12_381_Scalar))) :: ArithmeticCircuit (Zp BLS12_381_Scalar)

    putStrLn "\nExample: (<=) operation\n"

    putStrLn $ "Number of constraints: " ++ show (acSizeN ac)
    putStrLn $ "Number of variables: "   ++ show (acSizeM ac)