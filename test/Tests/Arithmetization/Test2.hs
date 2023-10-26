{-# LANGUAGE TypeApplications      #-}

module Tests.Arithmetization.Test2 (testArithmetization2) where

import           Prelude                                       hiding ((||), not, Num(..), Eq(..), Bool, (^), (/), replicate)

import           ZkFold.Base.Algebra.Basic.Field               (Zp)
import           ZkFold.Base.Algebra.Polynomials.GroebnerBasis (fromR1CS, verify, variableTypes)
import           ZkFold.Base.Data.Bool                         (BoolType(..), Bool (..))
import           ZkFold.Base.Data.Eq                           (Eq (..))
import           ZkFold.Base.Protocol.Arithmetization.R1CS     (compile)

import           Tests.Utility.Types                           (R, SmallField, Symbolic)

-- A true statement.
tautology :: forall a . Symbolic a => a -> a -> Bool a
tautology x y = (x /= y) || (x == y)

testArithmetization2 :: IO ()
testArithmetization2 = do
    let Bool r = compile @(Zp SmallField) (tautology @R) :: Bool R

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