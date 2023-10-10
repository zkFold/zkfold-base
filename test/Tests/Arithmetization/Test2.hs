{-# LANGUAGE TypeApplications      #-}

module Tests.Arithmetization.Test2 (testArithmetization2) where

import           Prelude                                     hiding ((||), not, Num(..), Eq(..), (^), (/), replicate)

import           ZkFold.Crypto.Algebra.Polynomials.GroebnerBasis (fromR1CS, verify)
import           ZkFold.Crypto.Data.Arithmetization          (Arithmetization(..))
import           ZkFold.Crypto.Data.Bool                     (GeneralizedBoolean(..), SymbolicBool (..))
import           ZkFold.Crypto.Data.Eq                       (GeneralizedEq (..))

import           Tests.Utility.Types                         (R)

-- A true statement.
testFunc :: forall a b . (GeneralizedEq b a) => a -> a -> b
testFunc x y = (x /= y) || (x == y)

testArithmetization2 :: IO ()
testArithmetization2 = do
    let r = compile @R (testFunc @R @(SymbolicBool R))

    putStrLn "\nStarting arithmetization test 2...\n"

    let theorem@(p0, ps) = fromR1CS r

    putStrLn "R1CS polynomials:\n"
    print ps
    putStrLn "\n\"The output equals 1\" polynomial:\n"
    print p0

    putStrLn "\nVerifying the theorem...\n"
    print $ verify theorem