{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.Arithmetization (testArithmetization) where

import           Data.List                                   (find)
import           Prelude                                     hiding (not, Num(..), Eq(..), (^), (/))

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Algebra.Basic.Field
import           ZkFold.Crypto.Protocol.Arithmetization.R1CS
import           ZkFold.Crypto.Data.Bool                     (GeneralizedBoolean(..), SymbolicBool (..))
import           ZkFold.Crypto.Data.Conditional              (GeneralizedConditional(..))
import           ZkFold.Crypto.Data.Eq                       (GeneralizedEq (..))
import           ZkFold.Crypto.Data.Symbolic                 (Symbolic(..))

data SmallField
instance Finite SmallField where
    order = 97
instance Prime SmallField

-- f x = if (2 / x == 3) then (x ^ 2 + 3 * x + 5) else (4 * x ^ 3)
testFunc :: forall a b . (FromConstant Integer a, FiniteField a, GeneralizedEq b a, GeneralizedConditional b a) => a -> a
testFunc x =
    let c  = fromConstant @Integer @a
        g1 = x ^ (2 :: Integer) + c 3 * x + c 5
        g2 = c 4 * x ^ (3 :: Integer)
        g3 = c 2 / x
    in (g3 == c 3 :: b) ? g1 $ g2 

testResult :: Zp SmallField -> Bool
testResult x =
    let r = compile (testFunc @(R1CS (Zp SmallField)) @(SymbolicBool (R1CS (Zp SmallField))))
        v = r1csValue $ apply @(R1CS (Zp SmallField)) @(R1CS (Zp SmallField)) r x
    in head v == testFunc @(Zp SmallField) @Bool x

testArithmetization :: IO ()
testArithmetization = do
    let m   = [0..order @SmallField - 1]
        res = zip m $ map (testResult . toZp) m
    case find (not . snd) res of
        Nothing     -> print @String "Success!"
        Just (i, _) -> do
            let r = compile (testFunc @(R1CS (Zp SmallField)) @(SymbolicBool (R1CS (Zp SmallField))))
                x = toZp i
            print @String $ "Failure at " ++ show i ++ "!"

            r1csPrint $ apply @(R1CS (Zp SmallField)) @(R1CS (Zp SmallField)) r x
            print $ testFunc @(Zp SmallField) @Bool x