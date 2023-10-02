{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE TypeApplications      #-}

module Tests.Arithmetization (testArithmetization) where

import           Data.Bifunctor                              (bimap)
import           Data.List                                   (find)
import           Prelude                                     hiding (not, Num(..), Eq(..), (^), (/))

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Algebra.Basic.Field
import           ZkFold.Crypto.Protocol.Arithmetization.R1CS
import           ZkFold.Crypto.Data.Arithmetization          (Arithmetization(..), applyArgs)
import           ZkFold.Crypto.Data.Bool                     (GeneralizedBoolean(..), SymbolicBool (..))
import           ZkFold.Crypto.Data.Conditional              (GeneralizedConditional(..))
import           ZkFold.Crypto.Data.Eq                       (GeneralizedEq (..))

import           Tests.Utility.Types                         (SmallField)

type R = R1CS (Zp SmallField) (Zp SmallField) Integer
type I = Integer

-- f x = if (2 / x == 3) then (x ^ 2 + 3 * x + 5) else (4 * x ^ 3)
testFunc :: forall a b . (FromConstant I a, FiniteField a, GeneralizedEq b a, GeneralizedConditional b a) => a -> a -> a
testFunc x y =
    let c  = fromConstant @I @a
        g1 = x ^ (2 :: I) + c 3 * x + c 5
        g2 = c 4 * x ^ (3 :: I)
        g3 = c 2 / x
    in (g3 == y :: b) ? g1 $ g2

testResult :: Zp SmallField -> Zp SmallField -> Bool
testResult x y =
    let r = compile (testFunc @R @(SymbolicBool R))
        v = r1csValue $ applyArgs @R @R r [x, y]
    in v == testFunc @(Zp SmallField) @Bool x y

testArithmetization :: IO ()
testArithmetization = do
    putStrLn "\nStarting arithmetization test...\n"
    let m   = zipWith (curry (bimap toZp toZp)) [0..order @SmallField - 1] [0..order @SmallField - 1]
        res = zip m $ map (uncurry testResult) m
    case find (not . snd) res of
        Nothing     -> putStrLn "Success!"
        Just (p@(x, y), _) -> do
            putStrLn $ "Failure at " ++ show p ++ "!"

            let r = compile (testFunc @R @(SymbolicBool R))
            r1csPrint $ applyArgs @R @R r [x, y]
            print $ testFunc @(Zp SmallField) @Bool x y