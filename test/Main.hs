{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications    #-}

module Main where

import           Prelude                              hiding (Num(..), (^), (/))

import           ZkFold.Crypto.Algebra.Basic.Class
import           ZkFold.Crypto.Algebra.Basic.Field
import           ZkFold.Crypto.Algebra.Symbolic.Bool  (SymbolicEq (..), SymbolicBool)
import           ZkFold.Crypto.Algebra.Symbolic.Class (Symbolic(..))
import           ZkFold.Crypto.Arithmetization.R1CS

-- TODO: move this elsewhere.
data SmallField
instance Finite SmallField where
    order = 7
instance Prime SmallField

-- f x = if (2 / x == 3) then (x ^ 2 + 3 * x + 5) else (4 * x ^ 3)
f :: forall a b . (FromConstant Integer a, FiniteField a, SymbolicEq b a) => a -> a
f x = 
    let c  = fromConstant @Integer @a
        g1 = x ^ (2 :: Integer) + c 3 * x + c 5
        g2 = c 4 * x ^ (3 :: Integer)
        g3 = c 2 / x
    in symIf (g3 $==$ c 3 :: b) g1 g2


main :: IO ()
main = do
    let 
        r = symbolic (f @(R1CS (Zp SmallField)) @(SymbolicBool (R1CS (Zp SmallField))))
        x = toZp 3

    r1csPrint $ eval @(R1CS (Zp SmallField)) @(R1CS (Zp SmallField)) r x
    print $ f @(Zp SmallField) @Bool x

    print @String "Success!"