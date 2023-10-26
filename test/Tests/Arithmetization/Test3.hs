{-# LANGUAGE TypeApplications      #-}

module Tests.Arithmetization.Test3 (testArithmetization3) where

import           Prelude                                     hiding (Num(..), Eq(..), Ord(..), Bool, (^), (/), (||), not, replicate)

import           ZkFold.Base.Algebra.Basic.Field             (Zp)
import           ZkFold.Base.Data.Bool                       (BoolType(..), Bool (..))
import           ZkFold.Base.Data.Ord                        (Ord (..))
import           ZkFold.Base.Protocol.Arithmetization.R1CS   (compile, r1csSizeM, r1csSizeN, r1csValue, applyArgs)

import           Tests.Utility.Types                         (R, SmallField, Symbolic)

-- A true statement.
testFunc :: forall a . Symbolic a => a -> a -> Bool a
testFunc x y = (x <= y) || (x > y)

testArithmetization3 :: IO ()
testArithmetization3 = do
    let Bool r = compile @(Zp SmallField) (testFunc @R) :: Bool R

    putStrLn "\nStarting arithmetization test 3...\n"

    putStr "System size: "
    print $ r1csSizeN r
    putStr "Variable size: "
    print $ r1csSizeM r

    putStr "Value (AC): "
    print $ r1csValue $ applyArgs r [3, 5]
    putStr "Value (function): "
    print $ testFunc @(Zp SmallField) 3 5