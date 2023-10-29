{-# LANGUAGE TypeApplications      #-}

module Tests.Arithmetization.Test2 (testArithmetization2) where

import           Prelude                         hiding (Num(..), Eq(..), Bool, (^), (/), (||), not, replicate)

import           ZkFold.Base.Algebra.Basic.Field (Zp)
import           ZkFold.Symbolic.Compiler        (compile)
import           ZkFold.Symbolic.Data.Bool       (BoolType(..), Bool (..))
import           ZkFold.Symbolic.Data.Eq         (Eq (..))
import           ZkFold.Symbolic.GroebnerBasis   (fromR1CS, verify, variableTypes)
import           ZkFold.Symbolic.Types           (R, SmallField, Symbolic)

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