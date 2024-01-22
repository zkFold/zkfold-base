{-# LANGUAGE TypeApplications    #-}

module Examples.MiMCHash (exampleMiMC) where

import           Prelude                                     hiding ((||), not, Num(..), Eq(..), (^), (/), (!!), any)

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Prelude                              ((!!), writeFileJSON)
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Conditional            (bool)
import           ZkFold.Symbolic.Types                       (Symbolic)

import           Examples.MiMC.Constants                     (mimcConstants)

-- | MiMC hash function
mimcHash :: forall a . Symbolic a => Integer -> a -> a -> a -> a
mimcHash nRounds k xL xR = 
    let c  = mimcConstants !! (nRounds-1)
        t5 = (xL + k + c) ^ (5 :: Integer)
    in bool (xR + t5) (mimcHash (nRounds-1) k (xR + t5) xL) (nRounds > 1)
          
exampleMiMC :: IO ()
exampleMiMC = do
    let nRounds = 220

    let ac   = compile @(Zp BLS12_381_Scalar) (mimcHash @(ArithmeticCircuit (Zp BLS12_381_Scalar)) nRounds zero) :: ArithmeticCircuit (Zp BLS12_381_Scalar)
        file = "compiled_scripts/mimcHash.json"

    putStrLn "\nExample: MiMC hash function\n"

    putStrLn $ "Number of constraints: " ++ show (acSizeN ac)
    putStrLn $ "Number of variables: "   ++ show (acSizeM ac)
    writeFileJSON file ac
    putStrLn $ "Script saved: " ++ file