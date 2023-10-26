{-# LANGUAGE TypeApplications      #-}

module Tests.Arithmetization.Test1 (testArithmetization1) where

import           Data.Bifunctor                              (bimap)
import           Data.List                                   (find)
import           Prelude                                     hiding ((||), not, Num(..), Eq(..), Bool, (^), (>), (/), replicate)
import qualified Prelude                                     as Haskell

import           ZkFold.Base.Algebra.Basic.Class
import           ZkFold.Base.Algebra.Basic.Field
import           ZkFold.Base.Protocol.Arithmetization.R1CS   (r1csPrint, r1csValue, applyArgs, compile)
import           ZkFold.Base.Data.Bool                       (BoolType(..), Bool (..))
import           ZkFold.Base.Data.Conditional                (Conditional(..))
import           ZkFold.Base.Data.Eq                         (Eq (..))

import           Tests.Utility.Types                         (SmallField, I, R, Symbolic)

-- f x y = if (2 / x > y) then (x ^ 2 + 3 * x + 5) else (4 * x ^ 3)
testFunc :: forall a . Symbolic a => a -> a -> a
testFunc x y =
    let c  = fromConstant @I @a
        g1 = x ^ (2 :: I) + c 3 * x + c 5
        g2 = c 4 * x ^ (3 :: I)
        g3 = c 2 / x
    in (g3 == y :: Bool a) ? g1 $ g2

testResult :: R -> Zp SmallField -> Zp SmallField -> Haskell.Bool
testResult r x y = r1csValue (applyArgs r [x, y]) == testFunc @(Zp SmallField) x y

testArithmetization1 :: IO ()
testArithmetization1 = do
    putStrLn "\nStarting arithmetization test 1...\n"
    putStrLn "Test sample:"
    let r = compile @(Zp SmallField) (testFunc @R)
    r1csPrint $ applyArgs r [3, 5]

    putStrLn "\nVerifying the circuit...\n"
    let m   = zipWith (curry (bimap toZp toZp)) [0..order @SmallField - 1] [0..order @SmallField - 1]
        res = zip m $ map (uncurry $ testResult r) m
    case find (not . snd) res of
        Nothing     -> putStrLn "Success!"
        Just (p@(x, y), _) -> do
            putStrLn $ "Failure at " ++ show p ++ "!"
            r1csPrint $ applyArgs r [x, y]
            print $ testFunc @(Zp SmallField) x y