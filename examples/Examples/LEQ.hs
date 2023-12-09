{-# LANGUAGE TypeApplications    #-}

module Examples.LEQ (exampleLEQ) where

import           Prelude                          hiding (Num(..), Eq(..), Ord(..), Bool, (^), (/), (!!), (||), not, any)

import           ZkFold.Base.Algebra.Basic.Field  (Zp)
import           ZkFold.Symbolic.Arithmetization  (acSizeM, acSizeN, ArithmeticCircuit)
import           ZkFold.Symbolic.Data.Bool        (Bool(..))
import           ZkFold.Symbolic.Data.Ord         (Ord(..))
import           ZkFold.Symbolic.Compiler         (compile)
import           ZkFold.Symbolic.Types            (Symbolic, BigField)

-- | (<=) operation
leq :: forall a . Symbolic a => a -> a -> Bool a
leq x y = x <= y
          
exampleLEQ :: IO ()
exampleLEQ = do
    let ac   = compile @(Zp BigField) (leq @(ArithmeticCircuit (Zp BigField))) :: ArithmeticCircuit (Zp BigField)

    putStrLn "\nExample: (<=) operation\n"

    putStrLn $ "Number of constraints: " ++ show (acSizeN ac)
    putStrLn $ "Number of variables: "   ++ show (acSizeM ac)