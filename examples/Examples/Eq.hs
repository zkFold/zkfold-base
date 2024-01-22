{-# LANGUAGE TypeApplications    #-}

module Examples.Eq (exampleEq) where

import           Prelude                                     hiding (Num(..), Eq(..), Ord(..), Bool, (^), (/), (!!), (||), not, any)

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Prelude                              (writeFileJSON)
import           ZkFold.Symbolic.Arithmetization             (acSizeM, acSizeN, ArithmeticCircuit)
import           ZkFold.Symbolic.Data.Bool                   (Bool(..))
import           ZkFold.Symbolic.Data.Eq                     (Eq(..))
import           ZkFold.Symbolic.Compiler                    (compile)
import           ZkFold.Symbolic.Types                       (Symbolic)

-- | (==) operation
eq :: forall a . Symbolic a => a -> a -> Bool a
eq x y = x == y
          
exampleEq :: IO ()
exampleEq = do
    let ac   = compile @(Zp BLS12_381_Scalar) (eq @(ArithmeticCircuit (Zp BLS12_381_Scalar))) :: ArithmeticCircuit (Zp BLS12_381_Scalar)
        file = "compiled_scripts/eq.json"

    putStrLn "\nExample: (==) operation\n"

    putStrLn $ "Number of constraints: " ++ show (acSizeN ac)
    putStrLn $ "Number of variables: "   ++ show (acSizeM ac)
    writeFileJSON file ac
    putStrLn $ "Script saved: " ++ file