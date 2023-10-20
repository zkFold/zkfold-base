{-# LANGUAGE TypeApplications      #-}

module Tests.Arithmetization.Test2 (testArithmetization2) where

import           Prelude                                     hiding ((||), not, Num(..), Eq(..), (^), (/), replicate)

import           ZkFold.Crypto.Algebra.Basic.Field           (Zp)
import           ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis (fromR1CS, verify, variableTypes)
import           ZkFold.Crypto.Data.Bool                     (GeneralizedBoolean(..), SymbolicBool (..))
import           ZkFold.Crypto.Data.Eq                       (GeneralizedEq (..))
import           ZkFold.Crypto.Protocol.Arithmetization.R1CS (compile)

import           Tests.Utility.Types                         (R, SmallField)

-- A true statement.
testFunc :: forall a b . (GeneralizedEq b a) => a -> a -> b
testFunc x y = (x /= y) || (x == y)

testArithmetization2 :: IO ()
testArithmetization2 = do
    let SymbolicBool r = compile @(Zp SmallField) (testFunc @R @(SymbolicBool R)) :: SymbolicBool R

    putStrLn "\nStarting arithmetization test 2...\n"

    let theorem@(p0, ps) = fromR1CS r

    putStrLn "R1CS polynomials:\n"
    print ps
    putStrLn "\n\"The output equals 1\" polynomial:\n"
    print p0
    putStrLn "\n\"Variable types:\n"
    print $ variableTypes ps

    putStrLn "\nVerifying the theorem...\n"
    print $ verify theorem