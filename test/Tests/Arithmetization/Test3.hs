{-# LANGUAGE TypeApplications      #-}

module Tests.Arithmetization.Test3 (testArithmetization3) where

import           Prelude                         hiding (Num(..), Eq(..), Ord(..), Bool, (^), (/), (||), not, any, replicate)

import           ZkFold.Base.Algebra.Basic.Field (Zp)
import           ZkFold.Symbolic.Arithmetization (compile, acSizeM, acSizeN, acValue, applyArgs, acValue)
import           ZkFold.Symbolic.Data.Bool       (Bool (..))
import           ZkFold.Symbolic.Data.Ord        (Ord (..))
import           ZkFold.Symbolic.Types           (R, SmallField, Symbolic)

-- A comparison test
testFunc :: forall a . Symbolic a => a -> a -> Bool a
testFunc x y = x <= y

testArithmetization3 :: IO ()
testArithmetization3 = do
    let Bool r = compile @(Zp SmallField) (testFunc @R) :: Bool R

    putStrLn "\nStarting arithmetization test 3...\n"

    putStr "System size: "
    print $ acSizeN r
    putStr "Variable size: "
    print $ acSizeM r

    putStr "Value (AC): "
    print $ acValue $ applyArgs r [3, 5]
    putStr "Value (function): "
    print $ testFunc @(Zp SmallField) 3 5