{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE TypeApplications      #-}

module Examples.Fibonacci (testArithmetization) where

import           Data.Bifunctor                              (bimap)
import           Data.List                                   (find)
import           Prelude                                     hiding ((||), not, Num(..), Eq(..), (^), (/), any)

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Algebra.Basic.Field
import           ZkFold.Crypto.Protocol.Arithmetization.R1CS
import           ZkFold.Crypto.Data.Arithmetization          (Arithmetization(..), applyArgs)
import           ZkFold.Crypto.Data.Bool                     (GeneralizedBoolean(..), SymbolicBool (..), any)
import           ZkFold.Crypto.Data.Conditional              (GeneralizedConditional(..))
import           ZkFold.Crypto.Data.Eq                       (GeneralizedEq (..))

import           Tests.Utility.Types                         (SmallField)
import qualified Prelude as Haskell
import Data.Map (singleton)

type R = R1CS (Zp SmallField) (Zp SmallField) Integer
type RB = R1CS (Zp SmallField) (SymbolicBool (Zp SmallField)) Integer
type I = Integer

-- inFibonacci100 :: forall a b . (FiniteField a, GeneralizedEq b a) => a -> b
-- inFibonacci100 x = any (\k -> fib k one one == x) [1..100]
--     where
--         fib :: I -> a -> a -> a
--         fib 1 x1 _  = x1
--         fib n x1 x2 = fib (n - 1) x2 (x1 + x2)

-- testResult :: Zp SmallField -> Bool
-- testResult x =
--     let r = compile @RB @(R -> RB) inFibonacci100
--         v = eval @RB @RB r $ singleton one x
--     in v == inFibonacci100 x

testArithmetization :: IO ()
testArithmetization = do
    putStrLn "\nStarting arithmetization test...\n"
--     let m   = map (SymbolicBool . toZp) [0..order @SmallField - 1]
--         res = zip m $ map testResult m
--     case find (not . snd) res of
--         Nothing     -> putStrLn "Success!"
--         Just (x@(SymbolicBool b), _) -> do
--             putStrLn $ "Failure at " ++ show x ++ "!"

--             let r = compile (inFibonacci100 @R @(SymbolicBool R))
--             r1csPrint $ applyArgs @RB @RB r [x]
--             print $ inFibonacci100 @(Zp SmallField) @(SymbolicBool (Zp SmallField)) b