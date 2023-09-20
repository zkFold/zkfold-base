{-# LANGUAGE TypeApplications #-}

module Main where

import           Prelude                              hiding (Num(..), (^))

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Algebra.Basic.Field
import           ZkFold.Crypto.Algebra.Symbolic.Class (Symbolic(..))
import           ZkFold.Crypto.Arithmetization.R1CS

-- TODO: move this elsewhere.
data SmallField
instance Finite SmallField where
    order = 7
instance Prime SmallField

-- f = x^2 + 3 x + 5
f :: forall a . (FromConstant Integer a, FiniteField a) => a -> a
f x = x ^ (2 :: Integer) + c 3 * x + c 5
    where c = fromConstant @Integer @a

main :: IO ()
main = do
    let 
        r = symbolic (f @(R1CS (Zp SmallField)))
        x = toZp 3

    r1csPrint $ eval @(R1CS (Zp SmallField)) @(R1CS (Zp SmallField)) r x
    print $ f x

    print @String "Success!"