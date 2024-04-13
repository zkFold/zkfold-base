{-# LANGUAGE TypeApplications #-}

module Examples.MiMCHash (exampleMiMC) where

import           Examples.MiMC.Constants                     (mimcConstants)
import           Numeric.Natural                             (Natural)
import           Prelude                                     hiding (Eq (..), Num (..), any, not, (!!), (/), (^), (||))

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Algebra.EllipticCurve.BLS12_381 (BLS12_381_Scalar)
import           ZkFold.Prelude                              ((!!))
import           ZkFold.Symbolic.Compiler
import           ZkFold.Symbolic.Data.Conditional            (bool)
import           ZkFold.Symbolic.Types                       (Symbolic)

-- | MiMC hash function
mimcHash :: forall a . Symbolic a => Natural -> a -> a -> a -> a
mimcHash nRounds k xL xR =
    let c  = mimcConstants !! (nRounds-!1)
        t5 = (xL + k + c) ^ (5 :: Natural)
    in bool (xR + t5) (mimcHash (nRounds-!1) k (xR + t5) xL) (nRounds > 1)

exampleMiMC :: IO ()
exampleMiMC = do
    let nRounds = 220
        file = "compiled_scripts/mimcHash.json"

    putStrLn "\nExample: MiMC hash function\n"

    compileIO @(Zp BLS12_381_Scalar) file (mimcHash @(ArithmeticCircuit (Zp BLS12_381_Scalar)) nRounds zero)
