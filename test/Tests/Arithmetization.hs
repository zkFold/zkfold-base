{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE PartialTypeSignatures #-}

module Tests.Arithmetization (testArithmetization) where

import           Control.Monad.State                         (execState)
import           Data.Bifunctor                              (bimap)
import           Data.List                                   (find)
import           Prelude                                     hiding (not, Num(..), Eq(..), (^), (/))

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Algebra.Basic.Field
import           ZkFold.Crypto.Protocol.Arithmetization.R1CS
import           ZkFold.Crypto.Data.Arithmetization          (Arithmetization(..))
import           ZkFold.Crypto.Data.Bool                     (GeneralizedBoolean(..), SymbolicBool (..))
import           ZkFold.Crypto.Data.Conditional              (GeneralizedConditional(..))
import           ZkFold.Crypto.Data.Eq                       (GeneralizedEq (..))

data SmallField
instance Finite SmallField where
    order = 97
instance Prime SmallField

type R = R1CS (Zp SmallField) (Zp SmallField)

-- f x = if (2 / x == 3) then (x ^ 2 + 3 * x + 5) else (4 * x ^ 3)
testFunc :: forall a b . (FromConstant Integer a, FiniteField a, GeneralizedEq b a, GeneralizedConditional b a) => a -> a -> a
testFunc x y =
    let c  = fromConstant @Integer @a
        g1 = x ^ (2 :: Integer) + c 3 * x + c 5
        g2 = c 4 * x ^ (3 :: Integer)
        g3 = c 2 / x
    in (g3 == y :: b) ? g1 $ g2

testResult :: Zp SmallField -> Zp SmallField -> Bool
testResult x y =
    let r = compile (testFunc @R @(SymbolicBool R))
        v = r1csValue $ flip execState r $ mapM (apply @R @R) [x, y]
    in v == testFunc @(Zp SmallField) @Bool x y

testArithmetization :: IO ()
testArithmetization = do
    let m   = zipWith (curry (bimap toZp toZp)) [0..order @SmallField - 1] [0..order @SmallField - 1]
        res = zip m $ map (uncurry testResult) m
    case find (not . snd) res of
        Nothing     -> print @String "Success!"
        Just (p@(x, y), _) -> do
            let r = compile (testFunc @R @(SymbolicBool R))
            print @String $ "Failure at " ++ show p ++ "!"

            r1csPrint $ flip execState r $ mapM (apply @R @R) [x, y]
            print $ testFunc @(Zp SmallField) @Bool x y